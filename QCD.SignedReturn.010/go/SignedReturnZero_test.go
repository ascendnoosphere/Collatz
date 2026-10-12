// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// quoTowardZero divides with arbitrary precision, truncating toward zero.
func quoTowardZero(a, d int64) int64 {
	return new(big.Int).Quo(big.NewInt(a), big.NewInt(d)).Int64()
}

// TestHandCases locks the three regimes, including negative divisors.
func TestHandCases(t *testing.T) {
	j, quot, ok := ZeroReturn(2, 0, 6)
	if !ok || j != 0 || quot != 3 {
		t.Fatalf("divisible seed: time %d quot %d ok %v", j, quot, ok)
	}
	if IsFirstHit(2, 0, 6, 1) {
		t.Fatal("later time was first after a hit at zero")
	}
	j, quot, ok = ZeroReturn(2, 0, 7)
	if !ok || j != 1 || quot != 0 {
		t.Fatalf("zero offset: time %d quot %d ok %v", j, quot, ok)
	}
	if PositiveSeedReturns(2, 7) {
		t.Fatal("positive seed returned under offset zero")
	}
	j, quot, ok = ZeroReturn(4, 12, 1)
	if !ok || j != 1 || quot != 3 {
		t.Fatalf("constant quotient: time %d quot %d ok %v", j, quot, ok)
	}
	j2, quot2, ok2 := ZeroReturn(4, 12, 7)
	if !ok2 || j2 != 1 || quot2 != quot {
		t.Fatal("constant quotient depended on the seed")
	}
	j, quot, ok = ZeroReturn(4, 12, 8)
	if !ok || j != 0 || quot != 2 {
		t.Fatal("an earlier hit was replaced by the offset quotient")
	}
	_, _, ok = ZeroReturn(5, 3, 2)
	if ok {
		t.Fatal("a double miss was given a return")
	}
	if IsFirstHit(5, 3, 2, 0) || IsFirstHit(5, 3, 2, 1) || IsFirstHit(5, 3, 2, 4) {
		t.Fatal("a double miss was called a first hit")
	}
	j, quot, ok = ZeroReturn(-3, 6, 1)
	if !ok || j != 1 || quot != -2 {
		t.Fatalf("negative divisor: time %d quot %d ok %v", j, quot, ok)
	}
	j, quot, ok = ZeroReturn(-3, 6, -3)
	if !ok || j != 0 || quot != 1 {
		t.Fatalf("negative seed: time %d quot %d ok %v", j, quot, ok)
	}
	if rawStep(6, -3, 1) != 6 || rawStep(6, -3, 6) != -2 {
		t.Fatal("raw return disagreed with c/d")
	}
}

// TestPositiveSeedNotTrue fails if PositiveSeedReturns is replaced by true.
func TestPositiveSeedNotTrue(t *testing.T) {
	divs := zeroDivisors[:]
	divs = divs[:len(divs)]
	for i := 0; i < len(divs); i++ {
		for n := int64(1); n <= int64(zeroNAbs); n++ {
			if PositiveSeedReturns(divs[i], n) {
				t.Fatalf("positive seed returned d=%d n=%d", divs[i], n)
			}
		}
	}
	// A nonzero divisible offset can return the seed. Offset zero cannot.
	j, quot, ok := ZeroReturn(2, 6, 3)
	if !ok || j != 1 || quot != 3 {
		t.Fatal("divisible offset did not return the seed")
	}
	if ZeroReturnMatchesSeed(2, 0, 3) {
		t.Fatal("offset zero returned the positive seed")
	}
}

// ZeroReturnMatchesSeed reports a positive-time return equal to the seed.
func ZeroReturnMatchesSeed(d, c, n int64) bool {
	j, quot, ok := ZeroReturn(d, c, n)
	return ok && j >= 1 && quot == n
}

// TestConstantQuotient checks that every missed seed returns c/d.
func TestConstantQuotient(t *testing.T) {
	divs := zeroDivisors[:]
	divs = divs[:len(divs)]
	for i := 0; i < len(divs); i++ {
		d := divs[i]
		for c := int64(-zeroCAbs); c <= int64(zeroCAbs); c++ {
			if !divides(d, c) {
				continue
			}
			want := quoTowardZero(c, d)
			if c/d != want {
				t.Fatalf("int64 quotient c=%d d=%d", c, d)
			}
			for n := int64(-zeroNAbs); n <= int64(zeroNAbs); n++ {
				if divides(d, n) {
					continue
				}
				j, quot, ok := ZeroReturn(d, c, n)
				if !ok || j != 1 || quot != want {
					t.Fatalf("d=%d c=%d n=%d time %d quot %d", d, c, n, j, quot)
				}
			}
		}
	}
}

// TestTrappedNotReturn fails if a double miss is reported as a return.
func TestTrappedNotReturn(t *testing.T) {
	if ZeroReturnGivesValue(5, 1, 1) {
		t.Fatal("trapped seed returned a value")
	}
	if ZeroReturnGivesValue(-4, 2, 1) {
		t.Fatal("negative trapped seed returned a value")
	}
	if IsFirstHit(5, 1, 1, 0) || IsFirstHit(5, 1, 1, 3) {
		t.Fatal("trapped predicate was true")
	}
}

// ZeroReturnGivesValue is the claim that a double miss still has a return.
// It is false. Replacing the body by true fails TestTrappedNotReturn.
func ZeroReturnGivesValue(d, c, n int64) bool {
	if divides(d, n) || divides(d, c) {
		return false
	}
	_, _, ok := ZeroReturn(d, c, n)
	return ok
}

// TestSignedQuotients matches exact division, including mixed signs.
func TestSignedQuotients(t *testing.T) {
	samples := [][3]int64{
		{-4, -12, 3},
		{-4, 12, -3},
		{4, -12, -3},
		{-5, 0, 0},
		{5, 0, 0},
	}
	for _, row := range samples {
		d, a, want := row[0], row[1], row[2]
		if a/d != want || quoTowardZero(a, d) != want {
			t.Fatalf("quotient d=%d a=%d", d, a)
		}
	}
}

// TestSweepCount pins the grid size and demands zero disagreements.
func TestSweepCount(t *testing.T) {
	if DomainChecks() != 196192 {
		t.Fatalf("domain %d", DomainChecks())
	}
	got := RunSweep()
	if got.Failures != 0 {
		t.Fatalf("failures %d", got.Failures)
	}
	if got.Checks != 196192 {
		t.Fatalf("checks %d", got.Checks)
	}
}
