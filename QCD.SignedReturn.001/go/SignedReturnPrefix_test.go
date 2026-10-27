// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// ReferenceOffset returns U_j(q) from the closed form (q^j-1)/(q-1), with the
// two degenerate cases U_0(q) = 0 and U_j(1) = j. The quotient is exact.
func ReferenceOffset(q int64, j int) *big.Int {
	if j == 0 {
		return big.NewInt(0)
	}
	if q == 1 {
		return big.NewInt(int64(j))
	}
	pow := new(big.Int).Exp(big.NewInt(q), big.NewInt(int64(j)), nil)
	num := new(big.Int).Sub(pow, big.NewInt(1))
	return num.Quo(num, big.NewInt(q-1))
}

// ReferenceAffine returns q^j*n + c*U_j(q) with big-integer arithmetic.
func ReferenceAffine(q, c int64, j int, n int64) *big.Int {
	pow := new(big.Int).Exp(big.NewInt(q), big.NewInt(int64(j)), nil)
	term := new(big.Int).Mul(pow, big.NewInt(n))
	offset := new(big.Int).Mul(big.NewInt(c), ReferenceOffset(q, j))
	return term.Add(term, offset)
}

// ReferenceStep applies one raw step with big-integer truncation toward zero.
func ReferenceStep(q, c, D int64, n *big.Int) *big.Int {
	bigD := big.NewInt(D)
	if new(big.Int).Rem(n, bigD).Sign() == 0 {
		return new(big.Int).Quo(n, bigD)
	}
	out := new(big.Int).Mul(big.NewInt(q), new(big.Int).Set(n))
	return out.Add(out, big.NewInt(c))
}

// ReferenceRaw returns the raw state at time j.
func ReferenceRaw(q, c, D, n int64, j int) *big.Int {
	cur := big.NewInt(n)
	for i := 0; i < j; i++ {
		cur = ReferenceStep(q, c, D, cur)
	}
	return cur
}

// ReferenceRawClean reports that no raw state before time j is divisible.
func ReferenceRawClean(q, c, D, n int64, j int) bool {
	cur := big.NewInt(n)
	bigD := big.NewInt(D)
	for i := 0; i < j; i++ {
		if new(big.Int).Rem(cur, bigD).Sign() == 0 {
			return false
		}
		cur = ReferenceStep(q, c, D, cur)
	}
	return true
}

// ReferenceAffineClean reports that no affine state before time j is divisible.
func ReferenceAffineClean(q, c, D, n int64, j int) bool {
	bigD := big.NewInt(D)
	for i := 0; i < j; i++ {
		if new(big.Int).Rem(ReferenceAffine(q, c, i, n), bigD).Sign() == 0 {
			return false
		}
	}
	return true
}

// ReferenceEqual reports whether the raw state and the affine state agree.
func ReferenceEqual(q, c, D, n int64, j int) bool {
	return ReferenceRaw(q, c, D, n, j).Cmp(ReferenceAffine(q, c, j, n)) == 0
}

// TestHandPrefixes locks the two sides to integers computed by hand, including
// a time after division where the sides differ.
func TestHandPrefixes(t *testing.T) {
	clean := []int64{1, 3}
	for j, want := range clean {
		if RawIterate(2, 1, 3, 1, j) != want || AffineState(2, 1, j, 1) != want {
			t.Fatalf("clean prefix at %d is not %d", j, want)
		}
		if !PrefixAgrees(2, 1, 3, 1, j) || !AffinePrefixAgrees(2, 1, 3, 1, j) {
			t.Fatalf("clean prefix at %d rejected", j)
		}
	}
	if RawIterate(2, 1, 3, 1, 2) != 1 || AffineState(2, 1, 2, 1) != 7 {
		t.Fatal("post-division states are not 1 and 7")
	}
	neg := []int64{-4, 11, -19, 41, -79, 161, -319}
	for j, want := range neg {
		if RawIterate(-2, 3, -5, -4, j) != want {
			t.Fatalf("negative raw prefix at %d: got %d", j, RawIterate(-2, 3, -5, -4, j))
		}
		if AffineState(-2, 3, j, -4) != want {
			t.Fatalf("negative affine prefix at %d: got %d", j, AffineState(-2, 3, j, -4))
		}
	}
}

// TestPredicateRejectsDividedPrefix fails if either identity predicate is
// replaced by a function that returns true on every input.
func TestPredicateRejectsDividedPrefix(t *testing.T) {
	if PrefixAgrees(2, 1, 3, 1, 2) {
		t.Fatal("forward predicate accepted a divided prefix")
	}
	if AffinePrefixAgrees(2, 1, 3, 1, 2) {
		t.Fatal("affine predicate accepted a divided prefix")
	}
	if PrefixAgrees(0, 2, 2, 1, 2) || AffinePrefixAgrees(0, 2, 2, 1, 2) {
		t.Fatal("zero multiplier accepted the time after division")
	}
	if RawIterate(0, 2, 2, 1, 2) == AffineState(0, 2, 2, 1) {
		t.Fatal("zero-multiplier sides agree after division")
	}
}

// TestGridMatchesClosedForm compares every int64 state with the closed form and
// requires both predicates to reject exactly the prefixes that are not clean.
func TestGridMatchesClosedForm(t *testing.T) {
	var checks uint64
	for q := int64(-prefixAbsCoeff); q <= prefixAbsCoeff; q++ {
		for c := int64(-prefixAbsCoeff); c <= prefixAbsCoeff; c++ {
			for _, D := range prefixDivisors {
				for n := int64(-prefixAbsSeed); n <= prefixAbsSeed; n++ {
					for j := 0; j <= prefixMaxJ; j++ {
						gotAff := big.NewInt(AffineState(q, c, j, n))
						wantAff := ReferenceAffine(q, c, j, n)
						if gotAff.Cmp(wantAff) != 0 {
							t.Fatalf("affine q=%d c=%d j=%d n=%d", q, c, j, n)
						}
						if gotAff.BitLen() > 16 {
							t.Fatalf("affine left the documented bound at %d %d %d %d",
								q, c, j, n)
						}
						gotRaw := big.NewInt(RawIterate(q, c, D, n, j))
						if gotRaw.Cmp(ReferenceRaw(q, c, D, n, j)) != 0 {
							t.Fatalf("raw q=%d c=%d D=%d n=%d j=%d", q, c, D, n, j)
						}
						rawClean := ReferenceRawClean(q, c, D, n, j)
						affClean := ReferenceAffineClean(q, c, D, n, j)
						equal := ReferenceEqual(q, c, D, n, j)
						if rawClean != RawPrefixClean(q, c, D, n, j) {
							t.Fatalf("raw guard q=%d c=%d D=%d n=%d j=%d", q, c, D, n, j)
						}
						if affClean != AffinePrefixClean(q, c, D, n, j) {
							t.Fatalf("affine guard q=%d c=%d D=%d n=%d j=%d", q, c, D, n, j)
						}
						if PrefixAgrees(q, c, D, n, j) != (rawClean && equal) {
							t.Fatalf("forward predicate q=%d c=%d D=%d n=%d j=%d",
								q, c, D, n, j)
						}
						if AffinePrefixAgrees(q, c, D, n, j) != (affClean && equal) {
							t.Fatalf("affine predicate q=%d c=%d D=%d n=%d j=%d",
								q, c, D, n, j)
						}
						checks++
						if rawClean != affClean {
							t.Fatalf("guards differ q=%d c=%d D=%d n=%d j=%d", q, c, D, n, j)
						}
						if rawClean {
							checks++
							if !equal {
								t.Fatalf("clean raw prefix disagrees at %d %d %d %d %d",
									q, c, D, n, j)
							}
						}
						if affClean {
							checks++
							if !equal {
								t.Fatalf("clean affine prefix disagrees at %d %d %d %d %d",
									q, c, D, n, j)
							}
						}
					}
				}
			}
		}
	}
	total := SweepPrefix()
	if total.Failures != 0 {
		t.Fatalf("sweep failures: %d", total.Failures)
	}
	if total.Checks != checks || checks == 0 {
		t.Fatalf("check count: sweep %d, reference %d", total.Checks, checks)
	}
}
