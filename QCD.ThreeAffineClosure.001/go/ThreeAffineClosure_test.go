// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestRejectsConstantTrue fails if every grid point is treated as closed.
func TestRejectsConstantTrue(t *testing.T) {
	constantTrue := func(a, b, c, q, x, y, z int64) bool {
		return true
	}
	a, b, c, q := int64(1), int64(1), int64(2), int64(1)
	x, y, z := int64(1), int64(1), int64(1)
	if !constantTrue(a, b, c, q, x, y, z) {
		t.Fatal("constant predicate was not constantly true")
	}
	if ClosureHolds(a, b, c, q, x, y, z) {
		t.Fatal("constant-true predicate accepted as closure")
	}
	if !ClosureHolds(1, 1, 1, 1, 1, 1, 1) {
		t.Fatal("closure predicate rejected every point")
	}
}

// TestKnownWitnesses checks the integer solutions used to read the identity.
func TestKnownWitnesses(t *testing.T) {
	type point struct {
		a, b, c, q    int64
		x, y, z       int64
		delta, first  int64
		third         int64
	}
	points := []point{
		{1, 1, 1, 1, 1, 1, 1, 7, 7, 7},
		{1, 1, 5, 5, 13, 33, 83, 3, 39, 249},
		{1, 3, 3, 5, 17, 43, 27, 3, 51, 81},
		{1, 1, 1, 3, -1, -1, -1, -19, 19, 19},
	}
	for _, p := range points {
		if DeltaValue(p.a, p.b, p.c, p.q) != p.delta {
			t.Fatalf("delta mismatch at q=%d", p.q)
		}
		if ClosureNumerator(p.a, p.b, p.q) != p.first {
			t.Fatalf("numerator mismatch at q=%d", p.q)
		}
		if ThirdComponent(p.c, p.a, p.q) != p.third {
			t.Fatalf("third component mismatch at q=%d", p.q)
		}
		if !EquationsHold(p.a, p.b, p.c, p.q, p.x, p.y, p.z) {
			t.Fatalf("equations failed at q=%d", p.q)
		}
		if !IdentityHolds(p.a, p.b, p.c, p.q, p.x, p.y, p.z) {
			t.Fatalf("identity failed at q=%d", p.q)
		}
		if p.z != p.third/p.delta {
			t.Fatalf("quotient mismatch at q=%d", p.q)
		}
	}
}

// TestNumeratorNotAlwaysDivisible records a word whose numerator is not a multiple.
func TestNumeratorNotAlwaysDivisible(t *testing.T) {
	delta := DeltaValue(1, 1, 2, 1)
	numerator := ClosureNumerator(1, 1, 1)
	if delta != 15 || numerator != 7 {
		t.Fatalf("expected delta 15 and numerator 7, got %d and %d",
			delta, numerator)
	}
	if numerator%delta == 0 {
		t.Fatal("non-multiple was reported as a multiple")
	}
	if ClosureHolds(1, 1, 2, 1, 1, 1, 1) {
		t.Fatal("non-solution was accepted")
	}
}

// TestGridIsFiniteCheck confirms the scan size and that the grid is not all closed.
func TestGridIsFiniteCheck(t *testing.T) {
	checks, witnesses, failures := ScanGrid()
	if checks != GridSize() {
		t.Fatalf("check count %d, grid size %d", checks, GridSize())
	}
	if failures != 0 {
		t.Fatalf("identity failures %d", failures)
	}
	if witnesses == 0 || witnesses == checks {
		t.Fatal("grid check collapsed to a constant predicate")
	}
}
