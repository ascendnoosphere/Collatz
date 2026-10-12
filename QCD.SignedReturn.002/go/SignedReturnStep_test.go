// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// referenceOffset returns U_j(q) from (q^j-1)/(q-1), with U_0(q) = 0 and
// U_j(1) = j. The quotient is exact for every integer q.
func referenceOffset(q int64, j int) *big.Int {
	if j == 0 {
		return big.NewInt(0)
	}
	if q == 1 {
		return big.NewInt(int64(j))
	}
	pow := new(big.Int).Exp(big.NewInt(q), big.NewInt(int64(j)), nil)
	num := new(big.Int).Sub(pow, big.NewInt(1))
	den := big.NewInt(q - 1)
	quot, rem := new(big.Int).QuoRem(num, den, new(big.Int))
	if rem.Sign() != 0 {
		panic("offset quotient was not exact")
	}
	return quot
}

// referenceAffine returns q^j*n + c*U_j(q) with big-integer arithmetic.
func referenceAffine(q, c int64, j int, n int64) *big.Int {
	pow := new(big.Int).Exp(big.NewInt(q), big.NewInt(int64(j)), nil)
	term := new(big.Int).Mul(pow, big.NewInt(n))
	offset := new(big.Int).Mul(big.NewInt(c), referenceOffset(q, j))
	return term.Add(term, offset)
}

// referenceDivides reports whether D divides n in big-integer arithmetic.
func referenceDivides(D int64, n *big.Int) bool {
	return new(big.Int).Rem(n, big.NewInt(D)).Sign() == 0
}

// referenceStep applies one raw step with big-integer truncation toward zero.
func referenceStep(q, c, D int64, n *big.Int) *big.Int {
	if referenceDivides(D, n) {
		return new(big.Int).Quo(n, big.NewInt(D))
	}
	out := new(big.Int).Mul(big.NewInt(q), new(big.Int).Set(n))
	return out.Add(out, big.NewInt(c))
}

// referenceRaw returns the raw state at time j.
func referenceRaw(q, c, D, n int64, j int) *big.Int {
	cur := big.NewInt(n)
	for i := 0; i < j; i++ {
		cur = referenceStep(q, c, D, cur)
	}
	return cur
}

// TestHandFirstHit locks both identities to integers computed by hand,
// including one division that leaves a factor of D.
func TestHandFirstHit(t *testing.T) {
	if !isFirstHit(2, 1, 3, 1, 1) || FirstHitStepHolds(2, 1, 3, 1, 1) != true {
		t.Fatal("seed 1 with q=2, c=1, D=3 does not hit at time 1")
	}
	if rawIterate(2, 1, 3, 1, 1) != 3 || affineState(2, 1, 1, 1) != 3 {
		t.Fatal("first hit state is not 3")
	}
	if rawStep(2, 1, 3, 3) != 1 {
		t.Fatal("one division of 3 by 3 is not 1")
	}
	if rawIterate(2, 1, 3, 1, 2) != 1 || affineState(2, 1, 2, 1) == 1 {
		t.Fatal("the state after the hit was confused with the next affine state")
	}
	if isFirstHit(5, 7, 2, -8, 0) != true {
		t.Fatal("seed -8 is not a first hit at time 0 for D=2")
	}
	if rawStep(5, 7, 2, -8) != -4 {
		t.Fatal("one division of -8 by 2 is not -4")
	}
	if !divides(2, -4) {
		t.Fatal("the quotient -4 no longer carries the remaining factor 2")
	}
	if rawStep(5, 7, 2, -8) == 1 || rawStep(5, 7, 2, -8) == -1 {
		t.Fatal("the check accepted removal of every factor of 2")
	}
	if !FirstHitStepHolds(5, 7, 2, -8, 0) {
		t.Fatal("time 0 rejected a divisible seed")
	}
	if !isFirstHit(-2, 1, 3, 1, 2) || !FirstHitStepHolds(-2, 1, 3, 1, 2) {
		t.Fatal("negative multiplier did not hit at time 2")
	}
	if affineState(-2, 1, 2, 1) != 3 || rawIterate(-2, 1, 3, 1, 2) != 3 {
		t.Fatal("negative multiplier state at time 2 is not 3")
	}
	if rawStep(-2, 1, 3, 3) != 1 {
		t.Fatal("division after the negative-multiplier hit is not 1")
	}
	if !FirstHitStepHolds(2, 1, -3, 1, 1) {
		t.Fatal("negative divisor rejected the hit at time 1")
	}
	if rawStep(2, 1, -3, 3) != -1 {
		t.Fatal("one division of 3 by -3 is not -1")
	}
}

// TestPredicateRejectsNonHit fails if FirstHitStepHolds is replaced by true.
func TestPredicateRejectsNonHit(t *testing.T) {
	if FirstHitStepHolds(2, 1, 3, 1, 0) {
		t.Fatal("predicate accepted a time before the first hit")
	}
	if FirstHitStepHolds(2, 1, 3, 1, 2) {
		t.Fatal("predicate accepted a time after the first hit")
	}
	for j := 0; j <= stepMaxJ; j++ {
		if isFirstHit(2, 0, 3, 1, j) || FirstHitStepHolds(2, 0, 3, 1, j) {
			t.Fatalf("predicate accepted the undivided power of two at %d", j)
		}
		if divides(3, rawIterate(2, 0, 3, 1, j)) {
			t.Fatalf("raw power of two was divisible by 3 at %d", j)
		}
	}
	if !rawPrefixUndivided(2, 0, 3, 1, stepMaxJ) {
		t.Fatal("undivided prefix was reported as divided")
	}
}

// TestGridAgreesWithBig compares the int64 grid with big-integer arithmetic.
// A constant-true predicate fails the non-hit branch. The grid is not a proof
// for parameters outside the stated rectangle.
func TestGridAgreesWithBig(t *testing.T) {
	var points uint64
	for q := int64(-stepAbsCoeff); q <= stepAbsCoeff; q++ {
		for c := int64(-stepAbsCoeff); c <= stepAbsCoeff; c++ {
			for _, D := range stepDivisors {
				for n := int64(-stepAbsSeed); n <= stepAbsSeed; n++ {
					points++
					hit := -1
					for j := 0; j <= stepMaxJ; j++ {
						aff := referenceAffine(q, c, j, n)
						gotAff := big.NewInt(affineState(q, c, j, n))
						if gotAff.Cmp(aff) != 0 {
							t.Fatalf("affine q=%d c=%d j=%d n=%d", q, c, j, n)
						}
						raw := referenceRaw(q, c, D, n, j)
						gotRaw := big.NewInt(rawIterate(q, c, D, n, j))
						if gotRaw.Cmp(raw) != 0 {
							t.Fatalf("raw q=%d c=%d D=%d n=%d j=%d", q, c, D, n, j)
						}
						if hit < 0 && referenceDivides(D, aff) {
							hit = j
						}
					}
					gotJ, ok := firstHitBy(q, c, D, n, stepMaxJ)
					if ok != (hit >= 0) || (ok && gotJ != hit) {
						t.Fatalf("hit q=%d c=%d D=%d n=%d", q, c, D, n)
					}
					if ok {
						if !FirstHitStepHolds(q, c, D, n, hit) {
							t.Fatalf("predicate rejected hit %d", hit)
						}
						aff := referenceAffine(q, c, hit, n)
						raw := referenceRaw(q, c, D, n, hit)
						if raw.Cmp(aff) != 0 {
							t.Fatalf("hit states differ at %d", hit)
						}
						next := referenceStep(q, c, D, raw)
						quot := new(big.Int).Quo(new(big.Int).Set(aff), big.NewInt(D))
						if next.Cmp(quot) != 0 {
							t.Fatalf("division mismatch at hit %d", hit)
						}
						back := new(big.Int).Mul(quot, big.NewInt(D))
						if back.Cmp(aff) != 0 {
							t.Fatalf("quotient did not recover the hit state")
						}
						for i := 0; i < hit; i++ {
							if FirstHitStepHolds(q, c, D, n, i) {
								t.Fatalf("predicate accepted time %d before %d", i, hit)
							}
						}
						continue
					}
					if !rawPrefixUndivided(q, c, D, n, stepMaxJ) {
						t.Fatalf("clean seed divided q=%d c=%d D=%d n=%d", q, c, D, n)
					}
					for j := 0; j <= stepMaxJ; j++ {
						if FirstHitStepHolds(q, c, D, n, j) {
							t.Fatalf("predicate accepted a non-hit at %d", j)
						}
						if referenceDivides(D, referenceRaw(q, c, D, n, j)) {
							t.Fatalf("raw prefix divided at %d", j)
						}
					}
				}
			}
		}
	}
	if points == 0 {
		t.Fatal("grid was empty")
	}
	total := sweepStep()
	if total.Failures != 0 {
		t.Fatalf("sweep failures: %d", total.Failures)
	}
	if total.Checks == 0 {
		t.Fatal("sweep recorded no checks")
	}
}
