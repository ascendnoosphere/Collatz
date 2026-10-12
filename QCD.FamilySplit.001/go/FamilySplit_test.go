// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestEvenGridAccepted checks exact parents on 1..64 and the check count.
func TestEvenGridAccepted(t *testing.T) {
	checks, ok := CheckEvenSplit(GridLimit)
	if !ok {
		t.Fatal("even split grid failed")
	}
	if checks != GridLimit {
		t.Fatalf("checks = %d, want %d", checks, GridLimit)
	}
	if checks != 64 {
		t.Fatalf("checks = %d, want 64", checks)
	}
}

// TestConstantTruePredicateRejected checks that a predicate which always
// returns true does not match even-row membership on the same grid.
func TestConstantTruePredicateRejected(t *testing.T) {
	if PredicatesAgree(GridLimit, ConstantTruePredicate) {
		t.Fatal("constantly true predicate matched the even split")
	}
}

// TestEvenSplitAgreesWithItself checks the membership predicate against itself.
func TestEvenSplitAgreesWithItself(t *testing.T) {
	if !PredicatesAgree(GridLimit, EvenSplitAt) {
		t.Fatal("even split predicate disagreed with itself")
	}
}

// TestThreeOutside checks that 3 is odd, its half is inexact, and its
// shortcut is not that truncated half.
func TestThreeOutside(t *testing.T) {
	if EvenSplitAt(3) {
		t.Fatal("3 was accepted in the even row")
	}
	if 3%2 != 1 {
		t.Fatal("3 was even")
	}
	if 2*(3/2) == 3 {
		t.Fatal("halving 3 was exact")
	}
	if Shortcut(3) != 5 || 3/2 != 1 {
		t.Fatalf("shortcut 3 = %d, half = %d", Shortcut(3), 3/2)
	}
}

// TestKnownEvenParents checks two even parents by direct arithmetic.
func TestKnownEvenParents(t *testing.T) {
	if !EvenSplitAt(2) || Shortcut(2) != 1 || 2*(2/2) != 2 {
		t.Fatal("parent of 2")
	}
	if !EvenSplitAt(12) || Shortcut(12) != 6 {
		t.Fatal("parent of 12")
	}
	if RunWord(evenSourceWord, 12) != 6 || RunWord(evenParentWord, 6) != 6 {
		t.Fatal("words for 12")
	}
	if EvenSplitAt(1) || EvenSplitAt(0) || EvenSplitAt(9) {
		t.Fatal("nonmember was accepted")
	}
}
