// SPDX-License-Identifier: CC-BY-4.0
package main

import "testing"

// TestRejectsConstantTrue fails if the unit test accepts every triple.
func TestRejectsConstantTrue(t *testing.T) {
	if IsUnitEqual(1, 3, 5) {
		t.Fatal("non-solution q=1, a=3, n=5 was accepted")
	}
	if !AlwaysTrue(1, 3, 5) {
		t.Fatal("control predicate did not accept the non-solution")
	}
	if IsUnitEqual(1, 3, 5) == AlwaysTrue(1, 3, 5) {
		t.Fatal("unit predicate agrees with a constantly true predicate")
	}
	if !IsUnitEqual(7, 3, 1) {
		t.Fatal("unit q=7, a=3, n=1 was rejected")
	}
	if IsUnitEqual(1, 3, 1) {
		t.Fatal("state 1 with the wrong multiplier was accepted")
	}
	if IsUnitEqual(7, 3, 3) {
		t.Fatal("state 3 was accepted")
	}
}

// TestUnequalNotClaimed fails if the grid is treated as an unequal-component theorem.
func TestUnequalNotClaimed(t *testing.T) {
	if UnequalComponentsExcluded() {
		t.Fatal("unequal components were marked excluded")
	}
	if AlwaysTrue(3, 1, 5) == UnequalComponentsExcluded() {
		t.Fatal("the unequal boundary agrees with a constantly true predicate")
	}
}

// TestClosureArithmetic checks the unit, a non-unit, unequal letters, and one factorization.
func TestClosureArithmetic(t *testing.T) {
	ws := Workspace{}
	if !ClosureHolds(&ws, 3, 1, 4) {
		t.Fatal("q=3, n=1, 2^2 failed")
	}
	if ClosureHolds(&ws, 3, 3, 4) {
		t.Fatal("q=3, n=3, 2^2 closed")
	}
	if ClosureHolds(&ws, 3, 5, 2) && ClosureHolds(&ws, 3, 5, 8) {
		t.Fatal("letters 1 and 3 both closed at n=5")
	}
	if (uint64(8)-1)*(8+1) != 64-1 {
		t.Fatal("difference of squares failed for 2^3 and q=1")
	}
}

// TestClosureOverflow rejects multiplication and final-addition overflow before comparison.
func TestClosureOverflow(t *testing.T) {
	ws := Workspace{}
	max := ^uint64(0)
	if ClosureHolds(&ws, max, 1, 0) {
		t.Fatal("overflowing q*n+1 was accepted as zero")
	}
	if ClosureHolds(&ws, max, 2, 1) || ClosureHolds(&ws, 1, 2, max) {
		t.Fatal("overflowing product was accepted")
	}
	if !ClosureHolds(&ws, max-1, 1, max) {
		t.Fatal("largest representable equal sides were rejected")
	}
}

// TestSweepCount matches Run with the closed count 208383 and allows no failures.
func TestSweepCount(t *testing.T) {
	cache := NewCache()
	checks, failures := Run(cache)
	if failures != 0 {
		t.Fatalf("failures %d", failures)
	}
	if checks != ExpectedChecks() {
		t.Fatalf("checks %d, expected %d", checks, ExpectedChecks())
	}
	if checks != 208383 {
		t.Fatalf("checks %d, expected 208383", checks)
	}
}
