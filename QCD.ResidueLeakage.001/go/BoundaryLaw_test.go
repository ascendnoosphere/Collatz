// SPDX-License-Identifier: CC-BY-4.0
package main

import "testing"

// TestBoundaryUniformLaw checks full marked-word coverage, moments, and exact drift controls.
func TestBoundaryUniformLaw(t *testing.T) {
	var w Workspace
	w.Initialize()
	for _, row := range []struct {
		q, depth, contracting uint64
	}{
		{3, 12, 3302},
		{5, 12, 1586},
	} {
		got, err := BoundaryCensus(Parameters{Q: row.q, C: 1, D: 2}, row.depth, &w)
		if err != nil {
			t.Fatal(err)
		}
		if got.DistinctWords != 1<<row.depth || got.ContractingWords != row.contracting {
			t.Fatalf("incorrect binary law: %+v", got)
		}
	}
	for _, p := range []Parameters{{Q: 4, C: 1, D: 3}, {Q: 5, C: 1, D: 4},
		{Q: 7, C: 1, D: 6}} {
		if _, err := BoundaryCensus(p, 5, &w); err != nil {
			t.Fatalf("full-cycle law failed for %+v: %v", p, err)
		}
	}
}

// TestBoundaryRejectsLeakage prevents a partial zero cycle from being treated as a full alphabet.
func TestBoundaryRejectsLeakage(t *testing.T) {
	var w Workspace
	w.Initialize()
	if _, err := BoundaryCensus(Parameters{Q: 2, C: 1, D: 3}, 4, &w); err == nil {
		t.Fatal("strict-leakage control was accepted as a full residue cycle")
	}
}

// TestBoundaryWarmedBuffers checks that repeated block ticks do not allocate in the hot loop.
func TestBoundaryWarmedBuffers(t *testing.T) {
	var w Workspace
	w.Initialize()
	w.Q.SetUint64(3)
	w.C.SetUint64(1)
	w.D.SetUint64(2)
	w.State.SetUint64(27)
	w.Multiplier.SetUint64(1)
	w.Block(2)
	allocs := testing.AllocsPerRun(100, func() {
		w.State.SetUint64(27)
		w.Multiplier.SetUint64(1)
		w.Block(2)
	})
	if allocs != 0 {
		t.Fatalf("warmed return block allocated %v times", allocs)
	}
}
