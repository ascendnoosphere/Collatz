// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// BigAffine returns A_j(q,c,n) by the affine recurrence in big integers.
func BigAffine(q, c, n int64, j int) *big.Int {
	cur := big.NewInt(n)
	qb := big.NewInt(q)
	cb := big.NewInt(c)
	for i := 0; i < j; i++ {
		cur.Mul(cur, qb)
		cur.Add(cur, cb)
	}
	return cur
}

// BigDivides reports that D divides z, with truncation toward zero.
func BigDivides(D int64, z *big.Int) bool {
	return new(big.Int).Rem(z, big.NewInt(D)).Sign() == 0
}

// BigIsFirstHit is the divisibility form of a first hit, read on big integers.
func BigIsFirstHit(q, c, D, n int64, j int) bool {
	for i := 0; i < j; i++ {
		if BigDivides(D, BigAffine(q, c, n, i)) {
			return false
		}
	}
	return BigDivides(D, BigAffine(q, c, n, j))
}

// TestPredicateRejectsNonHit fails if FirstHitBelowModulus is replaced by true.
func TestPredicateRejectsNonHit(t *testing.T) {
	if FirstHitBelowModulus(0, 0, 2, 1, 0) {
		t.Fatal("non-hit at time 0 was accepted")
	}
	if FirstHitBelowModulus(0, 1, 2, 1, 1) {
		t.Fatal("constant nonzero class was accepted")
	}
	if FirstHitBelowModulus(0, 0, 2, 0, 2) {
		t.Fatal("time equal to the modulus was accepted")
	}
	if FirstHitBelowModulus(1, 0, 3, 1, 4) {
		t.Fatal("time past the modulus was accepted")
	}
	if !FirstHitBelowModulus(0, 0, 2, 0, 0) {
		t.Fatal("zero seed at time 0 was rejected")
	}
	if !FirstHitBelowModulus(0, 0, 2, 1, 1) {
		t.Fatal("hit at time 1 was rejected")
	}
}

// TestHandOrbit locks the affine values and the hit time of two signed orbits.
func TestHandOrbit(t *testing.T) {
	// q = 2, c = 1, n = 1: states 1, 3, 7, 15. Modulus 5 hits at time 3.
	want := []int64{1, 3, 7, 15}
	for j, state := range want {
		if AffineAt(2, 1, 1, j) != state {
			t.Fatalf("affine state at %d is not %d", j, state)
		}
	}
	if !FirstHitBelowModulus(2, 1, 5, 1, 3) {
		t.Fatal("hit at time 3 was rejected")
	}
	if FirstHitBelowModulus(2, 1, 5, 1, 2) {
		t.Fatal("time 2 was accepted")
	}
	if !FirstHitBelowModulus(2, 1, -5, 1, 3) {
		t.Fatal("negative divisor rejected the hit at time 3")
	}
	if FirstHitBelowModulus(2, 1, -5, 1, 0) {
		t.Fatal("negative divisor accepted time 0")
	}
	// q = 1, c = 1, n = 1, modulus 4: states 1, 2, 3, 4, hit at time 3.
	acc := []int64{1, 2, 3, 4}
	for j, state := range acc {
		if AffineAt(1, 1, 1, j) != state {
			t.Fatalf("unit orbit at %d is not %d", j, state)
		}
	}
	if !IsFirstHit(1, 1, -4, 1, 3) || !FirstHitBelowModulus(1, 1, -4, 1, 3) {
		t.Fatal("modulus -4 did not hit at time 3")
	}
	if IsFirstHit(1, 1, 4, 1, 4) {
		t.Fatal("time 4 was a first hit")
	}
}

// TestModulusTwoCensus counts the six first hits among the eight residue triples.
func TestModulusTwoCensus(t *testing.T) {
	got := SweepModulus(2)
	if got.Failures != 0 {
		t.Fatalf("modulus 2 recorded %d failures", got.Failures)
	}
	if got.Hits != 6 {
		t.Fatalf("modulus 2 hits = %d, want 6", got.Hits)
	}
	if got.Checks != 30 {
		t.Fatalf("modulus 2 checks = %d, want 30", got.Checks)
	}
}

// TestCornerMatchesBig compares the largest grid state with big integers.
func TestCornerMatchesBig(t *testing.T) {
	const q, c, n int64 = 14, 14, 14
	const j = 15
	got := AffineAt(q, c, n, j)
	want := BigAffine(q, c, n, j)
	if !want.IsInt64() || got != want.Int64() {
		t.Fatalf("corner state %d disagrees with %s", got, want.String())
	}
}

// TestSignedSpotAgreesWithBig fails if a hit predicate is replaced by true.
func TestSignedSpotAgreesWithBig(t *testing.T) {
	var checks uint64
	for q := int64(-3); q <= 3; q++ {
		for c := int64(-3); c <= 3; c++ {
			for n := int64(-3); n <= 3; n++ {
				for _, D := range []int64{-3, -2, 2, 3} {
					mod := ModulusAbs(D)
					for j := 0; j <= 6; j++ {
						got := IsFirstHit(q, c, D, n, j)
						want := BigIsFirstHit(q, c, D, n, j)
						if got != want {
							t.Fatalf("hit q=%d c=%d D=%d n=%d j=%d", q, c, D, n, j)
						}
						below := FirstHitBelowModulus(q, c, D, n, j)
						if below != (want && j < int(mod)) {
							t.Fatalf("clock q=%d c=%d D=%d n=%d j=%d", q, c, D, n, j)
						}
						if want && j >= int(mod) {
							t.Fatalf("late hit q=%d c=%d D=%d n=%d j=%d", q, c, D, n, j)
						}
						checks++
					}
				}
			}
		}
	}
	if checks == 0 {
		t.Fatal("signed spot check was empty")
	}
}
