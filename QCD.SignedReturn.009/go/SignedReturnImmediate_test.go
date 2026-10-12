// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// bigQuotient returns the toward-zero quotient n/D as a big integer.
func bigQuotient(D, n int64) *big.Int {
	return new(big.Int).Quo(big.NewInt(n), big.NewInt(D))
}

// bigAbsProduct returns |D| * |n/D| with arbitrary-precision arithmetic.
func bigAbsProduct(D, n int64) *big.Int {
	quot := bigQuotient(D, n)
	return new(big.Int).Mul(new(big.Int).Abs(big.NewInt(D)), new(big.Int).Abs(quot))
}

// bigDivides reports that the big-integer remainder of n by D is zero.
func bigDivides(D, n int64) bool {
	rem := new(big.Int).Rem(big.NewInt(n), big.NewInt(D))
	return rem.Sign() == 0
}

// TestFirstHitRejectsNonMultiple fails if FirstHitAtZero is replaced by true.
func TestFirstHitRejectsNonMultiple(t *testing.T) {
	if FirstHitAtZero(2, 1) {
		t.Fatal("predicate accepted a non-multiple of 2")
	}
	if FirstHitAtZero(-5, 1) {
		t.Fatal("predicate accepted a non-multiple of -5")
	}
	if FirstHitAtZero(3, -1) {
		t.Fatal("predicate accepted a non-multiple of 3")
	}
	if FirstHitAtZero(-3, 2) {
		t.Fatal("predicate accepted a non-multiple of -3")
	}
}

// TestFirstHitAcceptsMultiple fails if FirstHitAtZero is replaced by false,
// and fails if the empty-range report is replaced by true.
func TestFirstHitAcceptsMultiple(t *testing.T) {
	if RangeNonempty(0) {
		t.Fatal("empty range reported an earlier hit")
	}
	if !FirstHitAtZero(2, 0) || !FirstHitAtZero(-2, -30) {
		t.Fatal("predicate rejected a multiple")
	}
	if !FirstHitAtZero(5, 30) || !FirstHitAtZero(-5, -30) {
		t.Fatal("predicate rejected an endpoint multiple")
	}
	if AffineAtZero(-2, 4, -30) != -30 || AffineAtZero(0, -3, 0) != 0 {
		t.Fatal("time-zero affine state is not the seed")
	}
}

// TestAbsProductRejectsRemainder fails if AbsProductExact is replaced by true.
func TestAbsProductRejectsRemainder(t *testing.T) {
	// 5 = 2*2 + 1, so |2| * |5/2| = 4, which is not 5.
	if AbsProductExact(2, 5) {
		t.Fatal("inexact quotient was accepted")
	}
	// -7 = (-3)*2 + (-1), so |-3| * |(-7)/(-3)| = 6, which is not 7.
	if AbsProductExact(-3, -7) {
		t.Fatal("inexact negative quotient was accepted")
	}
	if !AbsProductExact(-5, -30) {
		t.Fatal("exact quotient was rejected")
	}
	if abs64(-5)*abs64((-30)/(-5)) != 30 {
		t.Fatal("hand product is not 30")
	}
}

// TestCoreRejectsUnitModulus fails if CoreHolds is replaced by true.
func TestCoreRejectsUnitModulus(t *testing.T) {
	if CoreHolds(1, 0, 1, 8) {
		t.Fatal("A < |D| held at |D| = 1")
	}
	if CoreHolds(1, 0, -1, -8) {
		t.Fatal("A < |D| held at |D| = 1")
	}
	if CoreHolds(1, -1, 2, 4) {
		t.Fatal("strict slack below equality was accepted")
	}
	if !CoreHolds(1, 0, -5, 30) {
		t.Fatal("admissible exact quotient missed the bound")
	}
	if CoreHolds(1, 0, 0, 4) {
		t.Fatal("zero divisor satisfied the strict inequality")
	}
}

// TestGridAgreesWithBig compares every seed and signed divisor with big integers.
func TestGridAgreesWithBig(t *testing.T) {
	var divCount uint64
	for n := seedMin; n <= seedMax; n++ {
		for _, q := range zeroMultipliers {
			for _, c := range zeroOffsets {
				w := NewWorkspace()
				w.Prepare(q, c, 0)
				if w.Pow != 1 || w.Trap != 0 || w.Affine(n) != n {
					t.Fatalf("time zero q=%d c=%d n=%d", q, c, n)
				}
			}
		}
		for _, D := range signedDivisors {
			div := bigDivides(D, n)
			if Divides(D, n) != div {
				t.Fatalf("divisibility D=%d n=%d", D, n)
			}
			if FirstHitAtZero(D, n) != div {
				t.Fatalf("first hit D=%d n=%d", D, n)
			}
			prod := bigAbsProduct(D, n)
			wantAbs := new(big.Int).Abs(big.NewInt(n))
			exact := prod.Cmp(wantAbs) == 0
			if AbsProductExact(D, n) != exact {
				t.Fatalf("absolute product D=%d n=%d", D, n)
			}
			quot := bigQuotient(D, n)
			if !quot.IsInt64() || quot.Int64() != ImmediateReturn(D, n) {
				t.Fatalf("quotient D=%d n=%d", D, n)
			}
			if div {
				divCount++
				back := new(big.Int).Mul(big.NewInt(D), quot)
				if back.Cmp(big.NewInt(n)) != 0 {
					t.Fatalf("cancellation D=%d n=%d", D, n)
				}
				if !CoreHolds(1, 0, D, n) {
					t.Fatalf("core bound D=%d n=%d", D, n)
				}
			} else if exact {
				t.Fatalf("non-multiple had exact absolute product D=%d n=%d", D, n)
			}
		}
	}
	if divCount != 130 {
		t.Fatalf("divisible pairs = %d, want 130", divCount)
	}
}

// TestSweepCount pins the sweep and fails if a disagreement is ignored.
func TestSweepCount(t *testing.T) {
	total := RunSweep(NewCache())
	// 61 seeds, 9 time-zero pairs, 6 divisors, 130 divisible pairs.
	// Each seed contributes 9 affine checks. Each pair contributes one
	// hit comparison, plus three checks if divisible and one if not.
	const want = uint64(61*9 + 61*6 + 3*130 + 1*(61*6-130))
	if total.Failures != 0 {
		t.Fatalf("failures %d", total.Failures)
	}
	if total.Checks != want {
		t.Fatalf("checks %d, want %d", total.Checks, want)
	}
	if want != 1541 {
		t.Fatalf("pinned total changed to %d", want)
	}
}
