// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestGridAccepted checks the finite identities and records 295 comparisons.
func TestGridAccepted(t *testing.T) {
	checks, ok := CheckGrid()
	if !ok {
		t.Fatal("grid check failed")
	}
	if checks != 295 {
		t.Fatalf("checks = %d, want 295", checks)
	}
	if checks != ExpectedCheckCount() {
		t.Fatalf("checks = %d, count helper disagrees", checks)
	}
}

// TestConstantTruePredicateRejected checks that a predicate which always
// succeeds is not the positive gap.
func TestConstantTruePredicateRejected(t *testing.T) {
	var c Cache
	FillCache(&c)
	if StrictPositiveGap(&c, 1, 1) {
		t.Fatal("pair (1,1) was accepted as a positive gap")
	}
	if !ConstantTrue(1, 1) {
		t.Fatal("constant true predicate was false")
	}
	disagree := false
	for p := 1; p <= GridMax; p++ {
		for q := 1; q <= GridMax; q++ {
			if ConstantTrue(p, q) != StrictPositiveGap(&c, p, q) {
				disagree = true
			}
		}
	}
	if !disagree {
		t.Fatal("constant true predicate matched the gap")
	}
}

// TestWitnessOneTwo checks the numerator 23 and determinant 5.
func TestWitnessOneTwo(t *testing.T) {
	var c Cache
	var w Workspace
	FillCache(&c)
	word := w.Left[:3]
	word[0] = 1
	word[1] = 2
	word[2] = 2
	b := AccB(&c, 0, word)
	if b != 23 {
		t.Fatalf("numerator = %d, want 23", b)
	}
	delta := c.Pow2[1+4] - c.Pow3[1+2]
	if delta != 5 {
		t.Fatalf("determinant = %d, want 5", delta)
	}
	if Divides(delta, b) {
		t.Fatal("5 divided 23")
	}
	if Divides(delta, c.Pow3[1]-c.Pow2[1]) {
		t.Fatal("5 divided 1")
	}
}
