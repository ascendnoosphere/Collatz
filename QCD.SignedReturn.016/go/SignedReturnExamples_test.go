// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestSeedOne pins the first hit, affine state, and return of seed 1.
func TestSeedOne(t *testing.T) {
	j, state, ret, ok := FirstReturn(1)
	if !ok || j != 1 || state != 3 || ret != 1 {
		t.Fatalf("seed 1: ok %v j %d state %d return %d", ok, j, state, ret)
	}
	if !SatisfiesHitBound(1) {
		t.Fatal("seed 1 failed the return bound")
	}
}

// TestSeedFour pins the first hit, affine state, and return of seed 4.
func TestSeedFour(t *testing.T) {
	j, state, ret, ok := FirstReturn(4)
	if !ok || j != 1 || state != 9 || ret != 3 {
		t.Fatalf("seed 4: ok %v j %d state %d return %d", ok, j, state, ret)
	}
	if !SatisfiesHitBound(4) {
		t.Fatal("seed 4 failed the return bound")
	}
}

// TestSeedTwo pins the fixed residue and the absence of a first hit.
// An identically true hit predicate, or an identically true bound
// predicate, fails this test.
func TestSeedTwo(t *testing.T) {
	if EuclidMod(exQ*2+exC, exD) != 2 {
		t.Fatal("residue step did not fix 2")
	}
	if _, _, _, ok := FirstReturn(2); ok {
		t.Fatal("seed 2 was reported as a hit")
	}
	if SatisfiesHitBound(2) {
		t.Fatal("seed 2 satisfied the hit-bound predicate")
	}
}

// TestNegativeAndZero checks the sign of the quotient and the zero seed.
func TestNegativeAndZero(t *testing.T) {
	if _, _, _, ok := FirstReturn(-1); ok {
		t.Fatal("seed -1 was reported as a hit")
	}
	if SatisfiesHitBound(-1) {
		t.Fatal("seed -1 satisfied the hit-bound predicate")
	}
	j, state, ret, ok := FirstReturn(-2)
	if !ok || j != 1 || state != -3 || ret != -1 {
		t.Fatalf("seed -2: ok %v j %d state %d return %d", ok, j, state, ret)
	}
	if !SatisfiesHitBound(-2) {
		t.Fatal("seed -2 failed the return bound")
	}
	j, state, ret, ok = FirstReturn(0)
	if !ok || j != 0 || state != 0 || ret != 0 {
		t.Fatalf("seed 0: ok %v j %d state %d return %d", ok, j, state, ret)
	}
	if !SatisfiesHitBound(0) {
		t.Fatal("seed 0 failed the return bound")
	}
}

// TestSweepCounts pins the grid from -30 through 30.
// Replacing the bound predicate by true makes every trap a failure.
// Replacing it by false makes every hit a bound failure.
// TestFateControls pins one seed in each of the four outcomes.
// A classifier that sends every seed to zero fails the last three.
func TestFateControls(t *testing.T) {
	kind, at := ClassifyFate(0)
	if kind != "zero" || at != 0 || !TailAgrees(kind, at) {
		t.Fatalf("seed 0: %s %d", kind, at)
	}
	kind, at = ClassifyFate(1)
	if kind != "one" || at != 1 || !TailAgrees(kind, at) {
		t.Fatalf("seed 1: %s %d", kind, at)
	}
	kind, at = ClassifyFate(-1)
	if kind != "neg" || at != -1 || !TailAgrees(kind, at) {
		t.Fatalf("seed -1: %s %d", kind, at)
	}
	kind, at = ClassifyFate(2)
	if kind != "unbounded" || at != 2 || !TailAgrees(kind, at) {
		t.Fatalf("seed 2: %s %d", kind, at)
	}
	kind, at = ClassifyFate(4)
	if kind != "one" || at != 1 || !TailAgrees(kind, at) {
		t.Fatalf("seed 4: %s %d", kind, at)
	}
	kind, at = ClassifyFate(-2)
	if kind != "neg" || at != -1 || !TailAgrees(kind, at) {
		t.Fatalf("seed -2: %s %d", kind, at)
	}
}

// TestFatePartition checks that the four outcomes partition the grid.
func TestFatePartition(t *testing.T) {
	got := RunFates()
	sum := got.ToZero + got.ToOne + got.ToNegOne + got.Unbounded
	if got.Seeds != 61 || sum != 61 || got.Failures != 0 {
		t.Fatalf("seeds %d sum %d failures %d", got.Seeds, sum, got.Failures)
	}
	if got.ToZero != 1 || got.ToOne != 9 || got.ToNegOne != 13 ||
		got.Unbounded != 38 {
		t.Fatalf("zero %d one %d neg %d unbounded %d",
			got.ToZero, got.ToOne, got.ToNegOne, got.Unbounded)
	}
	if got.ToZero == 0 || got.ToOne == 0 || got.ToNegOne == 0 ||
		got.Unbounded == 0 {
		t.Fatal("one outcome was missing")
	}
}

// TestSweepCounts fixes the parameter grid's hit, trap and failure totals.
func TestSweepCounts(t *testing.T) {
	got := RunSweep()
	if got.Checks != 122 {
		t.Fatalf("checks %d", got.Checks)
	}
	if got.Hits != 41 || got.Traps != 20 {
		t.Fatalf("hits %d traps %d", got.Hits, got.Traps)
	}
	if got.BoundFailures != 0 || got.Failures != 0 {
		t.Fatalf("bound failures %d failures %d", got.BoundFailures, got.Failures)
	}
}
