// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestHalfGridAccepted checks the truncating half map on radius 8 through
// absolute value 32, including the outside contraction count 48 and the 65
// seeds from -32 through 32.
func TestHalfGridAccepted(t *testing.T) {
	step := func(n int) int {
		return HalfOutside(HalfRadius, n)
	}
	checks, ok := CheckHalf(HalfRadius, HalfLimit, step)
	if !ok {
		t.Fatal("half map failed entry or contraction")
	}
	if checks != 113 {
		t.Fatalf("half checks = %d, want 113", checks)
	}
	if checks != HalfCheckCount(HalfRadius, HalfLimit) {
		t.Fatalf("half checks = %d, count helper disagrees", checks)
	}
}

// TestIdentityRejected checks that the identity map is not accepted as a
// half-contraction on the same grid.
func TestIdentityRejected(t *testing.T) {
	id := func(n int) int { return n }
	checks, ok := CheckHalf(HalfRadius, HalfLimit, id)
	if ok {
		t.Fatal("identity map was accepted")
	}
	if checks != 113 {
		t.Fatalf("identity checks = %d, want 113", checks)
	}
}

// TestConstantTruePredicateRejected checks that a predicate which always
// returns true does not match the contraction predicate of the identity.
func TestConstantTruePredicateRejected(t *testing.T) {
	id := func(n int) int { return n }
	if PredicatesAgree(HalfRadius, HalfLimit, id, ConstantTruePredicate) {
		t.Fatal("constantly true predicate matched the identity")
	}
}

// TestKnownHalfOrbits checks entry values that are fixed by direct division.
func TestKnownHalfOrbits(t *testing.T) {
	step := func(n int) int {
		return HalfOutside(HalfRadius, n)
	}
	steps, ok := EntrySteps(HalfRadius, 32, step)
	if !ok || steps != 2 || HalfOutside(HalfRadius, 16) != 8 {
		t.Fatalf("orbit 32: steps=%d ok=%v", steps, ok)
	}
	steps, ok = EntrySteps(HalfRadius, 9, step)
	if !ok || steps != 1 || HalfOutside(HalfRadius, 9) != 4 {
		t.Fatalf("orbit 9: steps=%d ok=%v", steps, ok)
	}
	steps, ok = EntrySteps(HalfRadius, -17, step)
	if !ok || steps != 1 || HalfOutside(HalfRadius, -17) != -8 {
		t.Fatalf("orbit -17: steps=%d ok=%v", steps, ok)
	}
	steps, ok = EntrySteps(HalfRadius, -9, step)
	if !ok || steps != 1 || HalfOutside(HalfRadius, -9) != -4 {
		t.Fatalf("orbit -9: steps=%d ok=%v", steps, ok)
	}
	steps, ok = EntrySteps(HalfRadius, 8, step)
	if !ok || steps != 0 {
		t.Fatalf("orbit 8: steps=%d ok=%v", steps, ok)
	}
}

// TestAffineSpot checks one cleared iteration and one strict budget by hand.
func TestAffineSpot(t *testing.T) {
	num, den := IterateMajorant(1, 3, 1, 5, 3)
	if num != 18 || den != 27 {
		t.Fatalf("iterate = %d/%d, want 18/27", num, den)
	}
	if num*(3-1) != 1*(2*5-1)+27*1 {
		t.Fatal("cleared formula failed at h=3")
	}
	if !FormulaAgrees(1, 3, 1, 5, 3) || !BudgetImplies(1, 3, 1, 5, 3) {
		t.Fatal("library rejected the h=3 spot")
	}
	num, den = IterateMajorant(1, 3, 1, 5, 2)
	if num != 9 || den != 9 {
		t.Fatalf("iterate h=2 = %d/%d, want 9/9", num, den)
	}
	// The h=2 budget is not strict, and the iterate equals N0+1.
	left := 9 * ((0+1)*2 - 1)
	right := 1 * (2*5 - 1)
	if left > right || num < (0+1)*den {
		t.Fatal("h=2 spot is not the non-strict boundary")
	}
}

// TestAffineGridAccepted checks the nonnegative box and its test count.
func TestAffineGridAccepted(t *testing.T) {
	checks, ok := CheckAffine()
	if !ok {
		t.Fatal("affine grid failed")
	}
	if checks != AffineCheckCount() {
		t.Fatalf("affine checks = %d, helper = %d", checks, AffineCheckCount())
	}
	if AffineCheckCount() != 14850 {
		t.Fatalf("affine count = %d, want 14850", AffineCheckCount())
	}
}
