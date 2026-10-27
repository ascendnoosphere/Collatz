// SPDX-License-Identifier: CC-BY-4.0
//
// Exact certificate for QCD.Repunit.001. The program checks the repunit
// divisor identities, the exact multiplicative order, the unit cycle of the
// seed 1, the residue walk from 0, the trap set and the return map over a
// bounded grid, and reports the number of checks and the number of failures.

package main

import (
	"fmt"
	"math/big"
	"os"
	"sync"
)

const (
	repunitMaxQ    = 20 // multiplier bound of the sweeps
	repunitMaxK    = 20 // divisor-index bound of the sweeps
	repunitSeeds   = 200
	repunitSteps   = 24
	repunitWorkers = 4
)

// BigOne is the constant one shared by the sweeps.
var BigOne = big.NewInt(1)

// Totals counts the checks and the failures of one slice.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// Workspace holds the buffers reused by the step and return walks.
type Workspace struct {
	Sum  *big.Int
	Pow  *big.Int
	Cur  *big.Int
	Next *big.Int
	Rem  *big.Int
	Quot *big.Int
	Base *big.Int

	Repunits [2*repunitMaxK + 1]big.Int
	States   [repunitMaxK]big.Int
}

// NewWorkspace returns the arithmetic buffers and bounded state tables for one worker.
func NewWorkspace() *Workspace {
	return &Workspace{
		Sum:  new(big.Int),
		Pow:  new(big.Int),
		Cur:  new(big.Int),
		Next: new(big.Int),
		Rem:  new(big.Int),
		Quot: new(big.Int),
		Base: new(big.Int),
	}
}

// PrepareRepunits fills the bounded sum table once for the current multiplier.
func (w *Workspace) PrepareRepunits(q uint64) {
	w.Base.SetUint64(q)
	w.Repunits[0].SetUint64(0)
	for k := 1; k < len(w.Repunits); k++ {
		w.Repunits[k].Mul(&w.Repunits[k-1], w.Base)
		w.Repunits[k].Add(&w.Repunits[k], BigOne)
	}
}

// RepunitSum returns 1 + q + ... + q^(k-1) as a fresh value.
func RepunitSum(q uint64, k int) *big.Int {
	sum := new(big.Int)
	pow := big.NewInt(1)
	base := new(big.Int).SetUint64(q)
	for j := 0; j < k; j++ {
		sum.Add(sum, pow)
		pow.Mul(pow, base)
	}
	return sum
}

// StepBig applies one instruction with divisor D and unit offset at the state
// n, writing the result into out; out must be distinct from n and from D.
func (w *Workspace) StepBig(q uint64, D, n, out *big.Int) *big.Int {
	out.QuoRem(n, D, w.Rem)
	if w.Rem.Sign() == 0 {
		return out
	}
	out.Mul(w.Base.SetUint64(q), n)
	return out.Add(out, BigOne)
}

// Check records one failure when the condition fails.
func (t *Totals) Check(ok bool) {
	t.Checks++
	if !ok {
		t.Failures++
	}
}

// SweepDivisors checks the divisor identity (q-1) S_k = q^k - 1 and the
// divisibility S_k | q^k - 1 for every multiplier and index of the grid.
func SweepDivisors(q uint64, w *Workspace, t *Totals) {
	w.PrepareRepunits(q)
	w.Pow.SetUint64(1)
	for k := 1; k <= repunitMaxK; k++ {
		sum := &w.Repunits[k]
		w.Pow.Mul(w.Pow, w.Base.SetUint64(q))
		w.Next.Sub(w.Pow, BigOne)
		w.Cur.Mul(w.Base.SetUint64(q-1), sum)
		t.Check(w.Cur.Cmp(w.Next) == 0)
		w.Quot.QuoRem(w.Next, sum, w.Rem)
		t.Check(w.Rem.Sign() == 0)
	}
}

// SweepOrder checks that the order of q modulo S_k is exactly k: q^k = 1 and
// q^j is not 1 for 0 < j < k.
func SweepOrder(q uint64, w *Workspace, t *Totals) {
	w.PrepareRepunits(q)
	for k := 2; k <= repunitMaxK; k++ {
		sum := &w.Repunits[k]
		w.Pow.SetUint64(1)
		for j := 1; j <= k; j++ {
			w.Next.Mul(w.Pow, w.Base)
			w.Quot.QuoRem(w.Next, sum, w.Pow)
			t.Check((w.Pow.Cmp(BigOne) == 0) == (j == k))
		}
	}
}

// SweepCycle checks the orbit of the seed 1 with divisor S_k: the state after
// j steps is S_(j+1) for j < k and 1 at j = k, and no earlier state is 1.
func SweepCycle(q uint64, w *Workspace, t *Totals) {
	w.PrepareRepunits(q)
	for k := 2; k <= repunitMaxK; k++ {
		sum := &w.Repunits[k]
		w.Cur.SetUint64(1)
		for j := 1; j <= k; j++ {
			w.StepBig(q, sum, w.Cur, w.Next)
			w.Cur, w.Next = w.Next, w.Cur
			want := &w.Repunits[j+1]
			if j == k {
				want = BigOne
			}
			t.Check(w.Cur.Cmp(want) == 0)
			if j < k {
				t.Check(w.Cur.Cmp(BigOne) != 0)
			}
		}
	}
}

// SweepResidues checks the residue walk from 0 modulo S_k: the state after j
// steps is S_j, the walk returns to 0 after k steps, and the first k residues
// are pairwise distinct.
func SweepResidues(q uint64, w *Workspace, t *Totals) {
	w.PrepareRepunits(q)
	for k := 2; k <= repunitMaxK; k++ {
		sum := &w.Repunits[k]
		w.Cur.SetUint64(0)
		states := w.States[:k]
		for j := 1; j <= 2*k; j++ {
			w.Next.Mul(w.Base, w.Cur)
			w.Next.Add(w.Next, BigOne)
			w.Quot.QuoRem(w.Next, sum, w.Cur)
			w.Quot.QuoRem(&w.Repunits[j], sum, w.Rem)
			t.Check(w.Cur.Cmp(w.Rem) == 0)
			if j <= k {
				// Compare integers; decimal map keys would allocate on every tick.
				fresh := true
				for i := 0; i < j-1; i++ {
					if states[i].Cmp(w.Cur) == 0 {
						fresh = false
					}
				}
				t.Check(fresh)
				states[j-1].Set(w.Cur)
			}
		}
		// At time 2k the walk is back at the residue 0 of the starting state.
		t.Check(w.Cur.Sign() == 0)
	}
}

// SweepTraps checks that zero is the only state sent to zero by one
// instruction with divisor S_k and unit offset.
func SweepTraps(q uint64, w *Workspace, t *Totals) {
	w.PrepareRepunits(q)
	for k := 2; k <= repunitMaxK; k++ {
		sum := &w.Repunits[k]
		for n := 0; n <= repunitSeeds; n++ {
			w.Cur.SetUint64(uint64(n))
			w.StepBig(q, sum, w.Cur, w.Next)
			t.Check((w.Next.Sign() == 0) == (n == 0))
		}
	}
}

// SweepReturns checks that the return map fixes 1: after k-1 affine events the
// state is S_k, and dividing the multiple returns 1.
func SweepReturns(q uint64, w *Workspace, t *Totals) {
	w.PrepareRepunits(q)
	for k := 2; k <= repunitMaxK; k++ {
		w.Cur.SetUint64(1)
		w.Next.SetUint64(1)
		for j := 1; j < k; j++ {
			w.Next.Mul(w.Base.SetUint64(q), w.Cur)
			w.Next.Add(w.Next, BigOne)
			w.Cur, w.Next = w.Next, w.Cur
		}
		sum := &w.Repunits[k]
		t.Check(w.Cur.Cmp(sum) == 0)
		w.Next.QuoRem(w.Cur, sum, w.Rem)
		t.Check(w.Next.Cmp(BigOne) == 0)
	}
}

// SweepControls checks the boundaries of the family. The multiplier one
// controls are discriminating: the repunit sum degenerates to the index, and
// the order claim of the slice fails there because 1^j is one for every
// 0 < j < k, which the recorded witnesses assert. The divisor one makes every
// state fixed, and a divisor that is not a repunit sum gives no return to one
// within the horizon.
func SweepControls(w *Workspace, t *Totals) {
	w.PrepareRepunits(1)
	for k := 2; k <= repunitMaxK; k++ {
		sum := &w.Repunits[k]
		t.Check(sum.Cmp(w.Next.SetUint64(uint64(k))) == 0)
		w.Pow.SetUint64(1)
		for j := 1; j < k; j++ {
			w.Pow.Mul(w.Pow, BigOne)
			w.Quot.QuoRem(w.Pow, sum, w.Rem)
			t.Check(w.Rem.Cmp(BigOne) == 0)
		}
	}
	for q := uint64(2); q <= repunitMaxQ; q++ {
		for n := uint64(0); n <= 10; n++ {
			w.Cur.SetUint64(n)
			w.StepBig(q, BigOne, w.Cur, w.Next)
			t.Check(w.Next.Cmp(w.Cur) == 0)
		}
	}
	w.Cur.SetUint64(1)
	w.Sum.SetUint64(5)
	for j := 0; j < repunitSteps; j++ {
		w.StepBig(2, w.Sum, w.Cur, w.Next)
		w.Cur, w.Next = w.Next, w.Cur
		t.Check(w.Cur.Cmp(BigOne) != 0)
	}
}

// RunParallel sweeps q = 2..repunitMaxQ in chunks and sums the totals.
func RunParallel(fn func(uint64, *Workspace, *Totals)) Totals {
	chunks := make([]Totals, repunitWorkers)
	var wg sync.WaitGroup
	width := uint64(repunitMaxQ-1+repunitWorkers-1) / repunitWorkers
	for i := 0; i < repunitWorkers; i++ {
		lo := 2 + uint64(i)*width
		hi := lo + width - 1
		if hi > repunitMaxQ {
			hi = repunitMaxQ
		}
		if lo > hi {
			continue
		}
		wg.Add(1)
		go func(idx int, lo, hi uint64) {
			defer wg.Done()
			w := NewWorkspace()
			for q := lo; q <= hi; q++ {
				fn(q, w, &chunks[idx])
			}
		}(i, lo, hi)
	}
	wg.Wait()
	var total Totals
	for _, chunk := range chunks {
		total.Checks += chunk.Checks
		total.Failures += chunk.Failures
	}
	return total
}

// main runs every slice, prints the certificate and exits nonzero on failure.
func main() {
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
	var total Totals
	for _, slice := range slices {
		got := RunParallel(slice.run)
		fmt.Printf("%-9s checks %7d failures %d\n", slice.name, got.Checks, got.Failures)
		total.Checks += got.Checks
		total.Failures += got.Failures
	}
	control := Totals{}
	SweepControls(NewWorkspace(), &control)
	fmt.Printf("%-9s checks %7d failures %d\n", "controls", control.Checks, control.Failures)
	total.Checks += control.Checks
	total.Failures += control.Failures
	fmt.Printf("repunit divisor checks: %d, failures: %d\n", total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
