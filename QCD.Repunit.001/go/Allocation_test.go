//go:build !race

// SPDX-License-Identifier: CC-BY-4.0
// Allocation budgets apply to uninstrumented builds. Under -race, sync.Pool
// randomly discards entries used by math/big, invalidating zero-allocation counts.

package main

import (
	"math/big"
	"testing"
)

// TestWarmedAllocation requires the workspace walk to allocate nothing once its
// buffers have grown to the width of the walk. Every measured step works on
// multi-word states, and the two steps exercise the two branches of the step: a
// state that is not divisible follows the affine branch, and a multiple of the
// divisor follows the division branch.
func TestWarmedAllocation(t *testing.T) {
	w := NewWorkspace()
	divisor := new(big.Int).Lsh(big.NewInt(1), 100)
	divisor.Add(divisor, big.NewInt(1))
	odd := new(big.Int).Lsh(big.NewInt(1), 300)
	odd.Add(odd, big.NewInt(1))
	multiple := new(big.Int).Mul(divisor, odd)
	walk := func() {
		w.StepBig(3, divisor, odd, w.Cur)
		w.StepBig(3, divisor, multiple, w.Next)
	}
	walk()
	if w.Cur.BitLen() <= 64 || w.Next.BitLen() <= 64 {
		t.Fatalf("warmed walk stayed inside a word, widths %d and %d",
			w.Cur.BitLen(), w.Next.BitLen())
	}
	allocs := testing.AllocsPerRun(50, walk)
	if allocs != 0 {
		t.Fatalf("step walk allocated %v values per run", allocs)
	}
}

// TestWarmedSweepAllocations covers the complete sweeps, not just StepBig, so
// per-tick state copies and decimal residue keys cannot reappear unnoticed.
func TestWarmedSweepAllocations(t *testing.T) {
	slices := []struct {
		name string
		run  func(uint64, *Workspace, *Totals)
	}{
		{"divisors", SweepDivisors},
		{"order", SweepOrder},
		{"cycle", SweepCycle},
		{"residues", SweepResidues},
		{"traps", SweepTraps},
		{"returns", SweepReturns},
	}
	for _, slice := range slices {
		t.Run(slice.name, func(t *testing.T) {
			w := NewWorkspace()
			var total Totals
			walk := func() { slice.run(repunitMaxQ, w, &total) }
			walk()
			if got := testing.AllocsPerRun(20, walk); got != 0 {
				t.Fatalf("warmed sweep allocated %v values per run", got)
			}
			if total.Failures != 0 {
				t.Fatalf("warmed sweep failed %d checks", total.Failures)
			}
		})
	}
}
