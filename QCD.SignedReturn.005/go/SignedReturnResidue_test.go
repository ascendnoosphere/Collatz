// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// bigAffine returns q^j*n + c*U_j(q) with arbitrary-precision arithmetic.
func bigAffine(q, c, n int64, j int) *big.Int {
	pow := big.NewInt(1)
	trap := big.NewInt(0)
	qb := big.NewInt(q)
	for i := 0; i < j; i++ {
		trap.Add(trap, new(big.Int).Set(pow))
		pow.Mul(pow, qb)
	}
	term := new(big.Int).Mul(pow, big.NewInt(n))
	off := new(big.Int).Mul(big.NewInt(c), trap)
	return term.Add(term, off)
}

// bigResidue returns the representative of z in [0, m). The modulus is positive.
func bigResidue(z *big.Int, m int64) int64 {
	mod := new(big.Int).Mod(new(big.Int).Set(z), big.NewInt(m))
	return mod.Int64()
}

// TestHandAffine locks the negative orbit and the Mersenne prefix to integers
// computed by hand, including a negative divisor.
func TestHandAffine(t *testing.T) {
	neg := []int64{5, -17, 49, -149}
	negRes := []int64{1, 3, 1, 3}
	for j, want := range neg {
		if AffineValue(-3, -2, 5, j) != want {
			t.Fatalf("negative affine at %d is not %d", j, want)
		}
		if Residue(want, 4) != negRes[j] {
			t.Fatalf("negative residue at %d is not %d", j, negRes[j])
		}
		if ResidueWalk(-3, -2, 4, 5, j) != negRes[j] {
			t.Fatalf("negative walk at %d is not %d", j, negRes[j])
		}
		if !CastAgrees(-3, -2, -4, 5, j) {
			t.Fatalf("negative cast rejected at %d", j)
		}
	}
	mersenne := []int64{1, 3, 7, 15, 31}
	for j, want := range mersenne {
		if AffineValue(2, 1, 1, j) != want {
			t.Fatalf("mersenne affine at %d is not %d", j, want)
		}
	}
	if !IsFirstHit(2, 1, 5, 1, 3) || !IsFirstHit(2, 1, -5, 1, 3) {
		t.Fatal("time 3 is a first hit of the seed 1")
	}
	if !IsFirstHit(2, 1, 5, 6, 3) {
		t.Fatal("the congruent seed 6 lost the first hit")
	}
}

// TestCastIsRejectsSlack fails if CastIs or CastAgrees is replaced by true.
func TestCastIsRejectsSlack(t *testing.T) {
	if CastAgrees(2, 1, 0, 1, 0) || CastAgrees(2, 1, 1, 1, 0) ||
		CastAgrees(2, 1, -1, 1, 3) {
		t.Fatal("a divisor with absolute value below 2 was accepted")
	}
	if !CastAgrees(2, 1, 5, 1, 3) || !CastIs(2, 1, 5, 1, 3, 0) {
		t.Fatal("the zero class of 15 at time 3 was rejected")
	}
	if CastIs(2, 1, 5, 1, 3, 1) {
		t.Fatal("a unit slack from the zero class was accepted")
	}
	if CastIs(2, 1, 5, 1, 0, 0) {
		t.Fatal("time zero of the seed 1 was called zero")
	}
	if !CastIs(-3, -2, -4, 5, 1, 3) {
		t.Fatal("the class of -17 modulo 4 was rejected")
	}
	if CastIs(-3, -2, -4, 5, 1, 0) {
		t.Fatal("a wrong class of -17 was accepted")
	}
}

// TestFirstHitRejectsConstant fails if IsFirstHit is replaced by true or by false.
func TestFirstHitRejectsConstant(t *testing.T) {
	if IsFirstHit(1, 0, 2, 1, 0) || IsFirstHit(1, 0, 2, 3, 5) {
		t.Fatal("an odd seed was treated as a hit")
	}
	if !IsFirstHit(1, 0, 2, 4, 0) {
		t.Fatal("time zero is a first hit of the even seed")
	}
	if IsFirstHit(1, 0, 2, 4, 1) {
		t.Fatal("an earlier hit was ignored")
	}
	if IsFirstHit(2, 1, 5, 1, 2) || IsFirstHit(2, 1, 5, 1, 4) {
		t.Fatal("a time other than the first zero was marked first")
	}
	if IsFirstHit(2, 1, 1, 1, 0) || IsFirstHit(2, 1, 0, 1, 0) {
		t.Fatal("an inadmissible divisor was accepted as a hit")
	}
}

// TestAffineResidueMatchesBig compares every int64 affine residue on the grid
// with the same residue computed in arbitrary precision.
func TestAffineResidueMatchesBig(t *testing.T) {
	var checks uint64
	for q := int64(-castQAbs); q <= castQAbs; q++ {
		for c := int64(-castCAbs); c <= castCAbs; c++ {
			for m := int64(castDMin); m <= castDMax; m++ {
				for n := int64(-castNAbs); n <= castNAbs; n++ {
					for j := 0; j <= castJMax; j++ {
						got := Residue(AffineValue(q, c, n, j), m)
						want := bigResidue(bigAffine(q, c, n, j), m)
						if got != want {
							t.Fatalf("residue q=%d c=%d m=%d n=%d j=%d", q, c, m, n, j)
						}
						shift := Residue(AffineValue(q, c, n+m, j), m)
						if shift != got {
							t.Fatalf("shift q=%d c=%d m=%d n=%d j=%d", q, c, m, n, j)
						}
						checks++
					}
				}
			}
		}
	}
	// The big comparison uses positive moduli only, so it omits the sign of D.
	positive := CastDomainSize() / 2
	if checks != positive {
		t.Fatalf("big checks %d positive domain %d", checks, positive)
	}
}

// TestDomainAndSweep pins the grid size and demands zero disagreements.
func TestDomainAndSweep(t *testing.T) {
	if CastDomainSize() != 393822 {
		t.Fatalf("domain %d", CastDomainSize())
	}
	if ChecksPerPoint()*CastDomainSize() != 2756754 {
		t.Fatalf("check product %d", ChecksPerPoint()*CastDomainSize())
	}
	got := RunCastSweep()
	if got.Failures != 0 {
		t.Fatalf("residue failures %d", got.Failures)
	}
	if got.Checks != 2756754 {
		t.Fatalf("residue checks %d", got.Checks)
	}
}
