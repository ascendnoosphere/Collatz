// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// TestRejectsNonDivisible fails if either predicate is replaced by a function
// that returns true. The pair (4, 6) has truncating quotient 1, and 4*1 = 4,
// which is not 6. The pair (-5, 7) has truncating quotient -1, and
// (-5)*(-1) = 5, which is not 7. Neither pair is accepted by rounding.
func TestRejectsNonDivisible(t *testing.T) {
	if int64(6)/int64(4) != 1 {
		t.Fatal("6/4 did not truncate to 1")
	}
	if int64(4)*int64(1) == int64(6) {
		t.Fatal("truncated product unexpectedly reconstructed 6")
	}
	if ProductExact(4, 6) || AbsProductExact(4, 6) {
		t.Fatal("non-divisible pair 4, 6 was accepted")
	}
	if int64(7)/int64(-5) != -1 {
		t.Fatal("7/(-5) did not truncate to -1")
	}
	if int64(-5)*int64(-1) == int64(7) {
		t.Fatal("truncated product unexpectedly reconstructed 7")
	}
	if ProductExact(-5, 7) || AbsProductExact(-5, 7) {
		t.Fatal("negative divisor accepted a non-multiple")
	}
	if ProductExact(0, 0) || ProductExact(0, 5) || AbsProductExact(0, 12) {
		t.Fatal("zero divisor was accepted")
	}
}

// TestSignedProducts locks both equalities on every sign pattern, including a
// negative divisor and a zero dividend.
func TestSignedProducts(t *testing.T) {
	type row struct {
		D int64
		A int64
		Q int64
	}
	rows := []row{
		{D: 4, A: 12, Q: 3},
		{D: 4, A: -12, Q: -3},
		{D: -4, A: 12, Q: -3},
		{D: -4, A: -12, Q: 3},
		{D: -7, A: 21, Q: -3},
		{D: -7, A: -21, Q: 3},
		{D: 5, A: 0, Q: 0},
		{D: -5, A: 0, Q: 0},
	}
	for _, r := range rows {
		if r.A/r.D != r.Q || r.D*r.Q != r.A {
			t.Fatalf("hand quotient failed D=%d a=%d", r.D, r.A)
		}
		if absInt(r.D)*absInt(r.Q) != absInt(r.A) {
			t.Fatalf("hand absolute product failed D=%d a=%d", r.D, r.A)
		}
		if !ProductExact(r.D, r.A) || !AbsProductExact(r.D, r.A) {
			t.Fatalf("predicate rejected D=%d a=%d", r.D, r.A)
		}
	}
}

// TestAbsProductIsEquality checks a negative divisor: |-4| * |-3| = 12,
// which is |12|, with quotient -3 rather than a nonnegative substitute.
func TestAbsProductIsEquality(t *testing.T) {
	const D int64 = -4
	const a int64 = 12
	var w Workspace
	w.Load(D, a)
	if !w.Exact || w.Quot != -3 {
		t.Fatalf("expected quotient -3, got exact=%v quot=%d", w.Exact, w.Quot)
	}
	got := absInt(w.D) * absInt(w.Quot)
	if got != absInt(a) {
		t.Fatalf("absolute product %d, want %d", got, absInt(a))
	}
	if !AbsProductExact(D, a) {
		t.Fatal("absolute predicate rejected a negative divisor")
	}
}

// TestGridMatchesBig compares every grid pair with arbitrary-precision
// truncating division, including negative divisors and non-multiples.
func TestGridMatchesBig(t *testing.T) {
	cache := NewCache()
	var w Workspace
	for _, D := range cache.Divisors {
		bigD := big.NewInt(D)
		for _, a := range cache.States {
			w.Load(D, a)
			bigA := big.NewInt(a)
			rem := new(big.Int).Rem(new(big.Int).Set(bigA), bigD)
			divisible := rem.Sign() == 0
			if divisible != w.Exact {
				t.Fatalf("divisibility mismatch D=%d a=%d", D, a)
			}
			if !divisible {
				if w.Quot != 0 || ProductExact(D, a) || AbsProductExact(D, a) {
					t.Fatalf("non-multiple accepted D=%d a=%d", D, a)
				}
				continue
			}
			q := new(big.Int).Quo(new(big.Int).Set(bigA), bigD)
			if !q.IsInt64() || q.Int64() != w.Quot {
				t.Fatalf("quotient mismatch D=%d a=%d", D, a)
			}
			prod := new(big.Int).Mul(new(big.Int).Set(bigD), q)
			if prod.Cmp(bigA) != 0 || !ProductExact(D, a) {
				t.Fatalf("product mismatch D=%d a=%d", D, a)
			}
			absProd := new(big.Int).Mul(new(big.Int).Abs(bigD), new(big.Int).Abs(q))
			if absProd.Cmp(new(big.Int).Abs(bigA)) != 0 || !AbsProductExact(D, a) {
				t.Fatalf("absolute product mismatch D=%d a=%d", D, a)
			}
		}
	}
}
