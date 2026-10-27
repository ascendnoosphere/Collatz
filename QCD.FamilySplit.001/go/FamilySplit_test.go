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

// TestThreeOutside checks that 3 is excluded and follows the odd shortcut branch.
func TestThreeOutside(t *testing.T) {
	if EvenSplitAt(3) {
		t.Fatal("3 was accepted in the even row")
	}
	if got := Shortcut(3); got != 5 {
		t.Fatalf("shortcut 3 = %d, want 5", got)
	}
}

// TestKnownEvenParents checks two even parents by direct arithmetic.
func TestKnownEvenParents(t *testing.T) {
	if !EvenSplitAt(2) || Shortcut(2) != 1 {
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
