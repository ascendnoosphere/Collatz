// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestLargeSeedBreaksBound fails if the bound predicate accepts n=1001.
func TestLargeSeedBreaksBound(t *testing.T) {
	c := NewCache()
	c.Load(witnessQ)
	if !c.Live || c.Q != 2 {
		t.Fatal("cache was not loaded")
	}
	pow := c.W.Pow[:len(c.W.Pow)]
	trap := c.W.Trap[:len(c.W.Trap)]
	if pow[witnessJ] != 4 || trap[witnessJ] != 3 {
		t.Fatalf("power %d trap %d", pow[witnessJ], trap[witnessJ])
	}
	if witnessJ < 2 {
		t.Fatal("hit time is shorter than 2")
	}
	n, h, left, right, breaks := largeWitness(c)
	if n != 1001 || h != 1004 || left != 4016 || right != 4003 || !breaks {
		t.Fatalf("witness n=%d h=%d left=%d right=%d breaks=%t",
			n, h, left, right, breaks)
	}
	if !IsFirstHit(pow, trap, witnessC, witnessD, n, witnessJ) {
		t.Fatal("large seed lost the first hit")
	}
	if !IsFirstHit(pow, trap, witnessC, -witnessD, n, witnessJ) {
		t.Fatal("negative divisor lost the first hit")
	}
	aff := AffineAt(pow[witnessJ], trap[witnessJ], witnessC, n)
	if aff != 4016 || aff/witnessD != 1004 {
		t.Fatalf("affine %d quotient %d", aff, aff/witnessD)
	}
	if !QuotientProductMatches(witnessD, aff/witnessD, aff) {
		t.Fatal("exact product was rejected")
	}
	if 4*h <= 3*AbsInt(n)+1000 {
		t.Fatal("hand comparison did not break")
	}
	if ClassBoundHolds(4, h, 3, AbsInt(n), 1000) {
		t.Fatal("bound predicate accepted the large seed")
	}
}

// TestBoundNotConstant fails if the bound predicate is replaced by a constant.
func TestBoundNotConstant(t *testing.T) {
	if !ClassBoundHolds(4, 4, 3, 1, 1000) {
		t.Fatal("the seed 1 was expected to satisfy 4*4 <= 3*1+1000")
	}
	if ClassBoundHolds(4, 1004, 3, 1001, 1000) {
		t.Fatal("the seed 1001 was expected to reject the same pair")
	}
}

// TestProductRejectsSlack fails if the product predicate is replaced by true.
func TestProductRejectsSlack(t *testing.T) {
	if QuotientProductMatches(4, 1004, 4017) {
		t.Fatal("a unit slack was accepted")
	}
	if !QuotientProductMatches(4, 1004, 4016) {
		t.Fatal("the exact product was rejected")
	}
	if !QuotientProductMatches(-4, -1004, 4016) {
		t.Fatal("the negative quotient was rejected")
	}
}

// TestFirstHitNotConstant fails if the hit predicate is replaced by a constant.
func TestFirstHitNotConstant(t *testing.T) {
	c := NewCache()
	c.Load(2)
	pow := c.W.Pow[:len(c.W.Pow)]
	trap := c.W.Trap[:len(c.W.Trap)]
	if IsFirstHit(pow, trap, 4, 4, 1, 0) {
		t.Fatal("time zero divides the seed 1")
	}
	if IsFirstHit(pow, trap, 4, 4, 1, 1) {
		t.Fatal("time one divides the seed 1")
	}
	if !IsFirstHit(pow, trap, 4, 4, 1, 2) {
		t.Fatal("time two does not divide the seed 1")
	}
	if IsFirstHit(pow, trap, 4, 4, 2, 2) {
		t.Fatal("an earlier hit of the seed 2 was ignored")
	}
	if !IsFirstHit(pow, trap, 4, 4, 2, 1) {
		t.Fatal("time one is not the first hit of the seed 2")
	}
}

// TestClassMembership fails if class membership is replaced by true.
func TestClassMembership(t *testing.T) {
	if !SameClass(1001, 1, 4) {
		t.Fatal("1001 is not in the class of 1")
	}
	if !SameClass(-1199, 1, 4) {
		t.Fatal("-1199 is not in the class of 1")
	}
	if SameClass(2, 1, 4) {
		t.Fatal("2 was placed in the class of 1")
	}
	if SameClass(1, 1, 0) {
		t.Fatal("a zero divisor was accepted")
	}
}

// TestNegativeSeedBreaks checks one negative seed in the same class.
func TestNegativeSeedBreaks(t *testing.T) {
	c := NewCache()
	c.Load(2)
	pow := c.W.Pow[:len(c.W.Pow)]
	trap := c.W.Trap[:len(c.W.Trap)]
	n := int64(-1199)
	if !IsFirstHit(pow, trap, 4, 4, n, 2) {
		t.Fatal("negative seed lost the first hit")
	}
	h := QuotientAbs(pow[2], trap[2], 4, n, 4)
	if h != 1196 {
		t.Fatalf("absolute quotient %d", h)
	}
	if 4*h <= 3*AbsInt(n)+1000 {
		t.Fatal("hand comparison did not break for the negative seed")
	}
	if ClassBoundHolds(4, h, 3, AbsInt(n), 1000) {
		t.Fatal("bound predicate accepted the negative seed")
	}
}

// TestClassSweep checks the ray t=0 through 500 and rejects a constant bound.
func TestClassSweep(t *testing.T) {
	total := RunClassSweep()
	if total.Checks != 3006 {
		t.Fatalf("checks %d", total.Checks)
	}
	if total.Failures != 0 {
		t.Fatalf("failures %d", total.Failures)
	}
	if total.Holds != 247 || total.Breaks != 254 {
		t.Fatalf("holds %d breaks %d", total.Holds, total.Breaks)
	}
}
