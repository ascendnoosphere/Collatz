// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// bigAbsAffine returns |q^j*n + c*U_j(q)| with arbitrary-precision arithmetic.
func bigAbsAffine(q, c, n int64, j int) *big.Int {
	pow := big.NewInt(1)
	trap := big.NewInt(0)
	qb := big.NewInt(q)
	for i := 0; i < j; i++ {
		trap.Add(trap, new(big.Int).Set(pow))
		pow.Mul(pow, qb)
	}
	term := new(big.Int).Mul(pow, big.NewInt(n))
	off := new(big.Int).Mul(big.NewInt(c), trap)
	term.Add(term, off)
	return term.Abs(term)
}

// bigMajorant returns |q|^j*|n| + |c|*|U_j(q)| with arbitrary precision.
func bigMajorant(q, c, n int64, j int) *big.Int {
	absQ := big.NewInt(q)
	absQ.Abs(absQ)
	pow := new(big.Int).Exp(absQ, big.NewInt(int64(j)), nil)
	left := new(big.Int).Mul(pow, big.NewInt(abs64(n)))
	trap := big.NewInt(0)
	step := big.NewInt(1)
	qb := big.NewInt(q)
	for i := 0; i < j; i++ {
		trap.Add(trap, new(big.Int).Set(step))
		step.Mul(step, qb)
	}
	trap.Abs(trap)
	off := new(big.Int).Mul(big.NewInt(abs64(c)), trap)
	return left.Add(left, off)
}

// int64Exact converts a big integer that is known to fit in an int64.
func int64Exact(t *testing.T, z *big.Int) int64 {
	t.Helper()
	if !z.IsInt64() {
		t.Fatalf("value %s does not fit in int64", z.String())
	}
	return z.Int64()
}

// TestTriangleRejectsSlack fails if the triangle predicate is replaced by true.
func TestTriangleRejectsSlack(t *testing.T) {
	w := NewWorkspace()
	w.Load(2)
	// q = 2, j = 1, c = 1, n = -1.
	// The state is 2*(-1) + 1*1 = -1, and the majorant is 2*1 + 1*1 = 3.
	if w.TriangleLeft(1, -1, 1) != 1 || w.TriangleRight(1, -1, 1) != 3 {
		t.Fatalf("strict triangle sides %d and %d",
			w.TriangleLeft(1, -1, 1), w.TriangleRight(1, -1, 1))
	}
	right := w.TriangleRight(1, -1, 1)
	if !w.AffineTriangleAt(1, -1, 1, right) {
		t.Fatal("strict triangle was rejected")
	}
	if w.AffineTriangleAt(1, -1, 1, right-1) {
		t.Fatal("a majorant decreased by one was accepted")
	}
	if w.AffineTriangleAt(1, -1, 1, right+1) {
		t.Fatal("a majorant increased by one was accepted")
	}
	// Same data with aligned signs: state 2*1 + 1 = 3, majorant 3.
	if w.TriangleLeft(1, 1, 1) != w.TriangleRight(1, 1, 1) {
		t.Fatal("aligned terms were not equal")
	}
}

// TestReturnRejectsNonHit fails if the return predicate is replaced by true.
func TestReturnRejectsNonHit(t *testing.T) {
	w := NewWorkspace()
	w.Load(2)
	// Time zero at seed 1 is not a hit for divisor 3.
	if w.IsFirstHit(1, 3, 1, 0) {
		t.Fatal("3 divides 1")
	}
	if w.ReturnMagnitudeAt(1, 3, 1, 0, 0, 0) {
		t.Fatal("a non-hit was accepted")
	}
	// Time zero at seed 3 is a hit. Both sides equal 3.
	if !w.IsFirstHit(1, 3, 3, 0) {
		t.Fatal("3 does not divide 3 at time zero")
	}
	if w.QuotientMagnitude(1, 3, 3, 0) != 3 || w.TriangleRight(1, 3, 0) != 3 {
		t.Fatal("time-zero magnitudes are not 3 and 3")
	}
	if !w.ReturnMagnitudeAt(1, 3, 3, 0, 3, 3) {
		t.Fatal("time-zero hit was rejected")
	}
	if w.ReturnMagnitudeAt(1, 3, 3, 0, 4, 3) {
		t.Fatal("a quotient magnitude increased by one was accepted")
	}
	if w.ReturnMagnitudeAt(1, 3, 3, 0, 3, 2) {
		t.Fatal("a majorant decreased by one was accepted")
	}
	// An earlier hit blocks a later time: seed 2, divisor 2, time 1.
	if w.IsFirstHit(0, 2, 2, 1) {
		t.Fatal("an earlier hit was ignored")
	}
	if w.ReturnMagnitudeAt(0, 2, 2, 1, 0, 0) {
		t.Fatal("a later time after a hit was accepted")
	}
}

// TestNegativeQuotient checks a negative divisor and a negative seed.
func TestNegativeQuotient(t *testing.T) {
	w := NewWorkspace()
	w.Load(-2)
	// j = 0, n = -8, d = -4. The quotient is 2, and |-4|*|2| = 8.
	if !w.IsFirstHit(5, -4, -8, 0) {
		t.Fatal("negative divisor rejected a multiple at time zero")
	}
	if w.QuotientMagnitude(5, -4, -8, 0) != 8 {
		t.Fatalf("quotient magnitude %d", w.QuotientMagnitude(5, -4, -8, 0))
	}
	if w.TriangleRight(5, -8, 0) != 8 {
		t.Fatalf("time-zero majorant %d", w.TriangleRight(5, -8, 0))
	}
	if !w.ReturnMagnitudeAt(5, -4, -8, 0, 8, 8) {
		t.Fatal("negative quotient identity was rejected")
	}
	// q = -2, j = 1, c = 4, n = 1, d = 2.
	// State -2 + 4 = 2. Time zero is the seed 1, which 2 does not divide.
	if !w.IsFirstHit(4, 2, 1, 1) {
		t.Fatal("expected a first hit at time one")
	}
	if w.QuotientMagnitude(4, 2, 1, 1) != 2 {
		t.Fatal("time-one quotient magnitude is not 2")
	}
	if w.TriangleRight(4, 1, 1) != 6 {
		t.Fatal("time-one majorant is not 6")
	}
	if !w.ReturnMagnitudeAt(4, 2, 1, 1, 2, 6) {
		t.Fatal("strict return bound was rejected")
	}
}

// TestCornersMatchBig compares int64 sides with arbitrary-precision sides.
func TestCornersMatchBig(t *testing.T) {
	w := NewWorkspace()
	qs := []int64{magQMin, -1, 0, 1, magQMax}
	js := []int{0, 1, magJMax}
	cs := []int64{magCMin, 0, magCMax}
	ns := []int64{magNMin, -1, 0, 1, magNMax}
	for _, q := range qs {
		w.Load(q)
		for _, j := range js {
			if abs64(w.Pow[j]) >= magBudget {
				t.Fatalf("power budget failed at q=%d j=%d", q, j)
			}
			for _, c := range cs {
				for _, n := range ns {
					left := w.TriangleLeft(c, n, j)
					right := w.TriangleRight(c, n, j)
					wantL := int64Exact(t, bigAbsAffine(q, c, n, j))
					wantR := int64Exact(t, bigMajorant(q, c, n, j))
					if left != wantL || right != wantR {
						t.Fatalf("corner mismatch q=%d c=%d n=%d j=%d", q, c, n, j)
					}
					if left > right {
						t.Fatalf("corner triangle failed q=%d j=%d", q, j)
					}
					if !w.AffineTriangleAt(c, n, j, right) {
						t.Fatalf("corner predicate rejected q=%d j=%d", q, j)
					}
				}
			}
		}
	}
}

// TestSweepDomain demands the full grid, zero disagreements, and both outcomes.
func TestSweepDomain(t *testing.T) {
	qCount := uint64(magQMax - magQMin + 1)
	cCount := uint64(magCMax - magCMin + 1)
	nCount := uint64(magNMax - magNMin + 1)
	jCount := uint64(magJMax + 1)
	triangle := qCount * cCount * nCount * jCount
	if TriangleDomain() != triangle {
		t.Fatalf("triangle domain %d product %d", TriangleDomain(), triangle)
	}
	if ReturnDomain() != triangle*uint64(len(magnitudeDivisors)) {
		t.Fatalf("return domain %d", ReturnDomain())
	}
	if BudgetDomain() != qCount*jCount {
		t.Fatalf("budget domain %d", BudgetDomain())
	}
	if SweepDomain() != BudgetDomain()+TriangleDomain()+ReturnDomain() {
		t.Fatal("sweep domain is not the sum of its parts")
	}
	got := sweepAll()
	if got.Checks != SweepDomain() || got.Failures != 0 {
		t.Fatalf("magnitude checks %d failures %d domain %d",
			got.Checks, got.Failures, SweepDomain())
	}
}
