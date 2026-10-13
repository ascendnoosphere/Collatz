// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math"
	"math/big"
	"testing"
)

// Cache reuses exact rational operands in the independent reference calculation.
type Cache struct {
	rho, mu, ratio big.Rat
	left, right    big.Rat
	two, four      big.Rat
}

// Init sets the two constant multipliers once, outside the grid loop.
func (c *Cache) Init() {
	c.two.SetInt64(2)
	c.four.SetInt64(4)
}

// ReferenceFlags derives comparisons from fractions, not the cleared predicates.
func (c *Cache) ReferenceFlags(n uint64) [7]bool {
	k := int64(n)
	c.rho.SetFrac64(1, k*(k+1))
	c.mu.SetFrac64(2, k*(k-1))
	c.left.Mul(&c.two, &c.rho)
	lower := c.left.Cmp(&c.mu) <= 0
	c.right.Mul(&c.four, &c.rho)
	upper := c.mu.Cmp(&c.right) <= 0
	c.ratio.Quo(&c.mu, &c.rho)
	c.right.SetFrac64(2*(k+1), k-1)
	ratio := c.ratio.Cmp(&c.right) == 0
	scalarLower := c.two.Cmp(&c.ratio) <= 0
	scalarUpper := c.ratio.Cmp(&c.four) <= 0
	c.left.SetFrac64(1, k)
	c.right.SetFrac64(1, k+1)
	c.left.Sub(&c.left, &c.right)
	rhoStep := c.left.Cmp(&c.rho) == 0
	c.left.SetFrac64(2, k-1)
	c.right.SetFrac64(2, k)
	c.left.Sub(&c.left, &c.right)
	muStep := c.left.Cmp(&c.mu) == 0
	return [7]bool{lower, upper, ratio, scalarLower, scalarUpper, rhoStep, muStep}
}

// TestReferenceGrid checks the observed truth values, including the false n=2 bound.
func TestReferenceGrid(t *testing.T) {
	var c Cache
	c.Init()
	for n := uint64(2); n <= GridMax; n++ {
		got := [7]bool{
			TwoRhoLeMu(n), MuLeFourRho(n), RatioAgrees(n),
			RatioAtLeastTwo(n), RatioAtMostFour(n), RhoStep(n), MuStep(n),
		}
		want := c.ReferenceFlags(n)
		if got != want {
			t.Fatalf("n=%d got=%v want=%v", n, got, want)
		}
	}
	if !RhoStep(1) || RhoDen(1) != 2 {
		t.Fatal("rho telescope failed at n=1")
	}
}

// ReferenceWindow sums fractions directly, without invoking Rat or the closed forms.
func ReferenceWindow(lo, hi uint64, mu bool) *big.Rat {
	var sum, term big.Rat
	for n := lo; n <= hi; n++ {
		k := int64(n)
		if mu {
			term.SetFrac64(2, k*(k-1))
		} else {
			term.SetFrac64(1, k*(k+1))
		}
		sum.Add(&sum, &term)
	}
	return &sum
}

// TestRationalWindows checks all bounded windows, including empty ones, by big.Rat.
func TestRationalWindows(t *testing.T) {
	var got big.Rat
	for hi := uint64(0); hi <= WitnessMax; hi++ {
		for lo := uint64(1); lo <= hi+1; lo++ {
			r := SumRho(lo, hi)
			got.SetFrac64(r.num, r.den)
			want := ReferenceWindow(lo, hi, false)
			if got.Cmp(want) != 0 {
				t.Fatalf("rho [%d,%d] got=%s want=%s", lo, hi, &got, want)
			}
		}
	}
	for hi := uint64(1); hi <= WitnessMax; hi++ {
		for lo := uint64(2); lo <= hi+1; lo++ {
			r := SumMu(lo, hi)
			got.SetFrac64(r.num, r.den)
			want := ReferenceWindow(lo, hi, true)
			if got.Cmp(want) != 0 {
				t.Fatalf("mu [%d,%d] got=%s want=%s", lo, hi, &got, want)
			}
		}
	}
}

// TestRationalOperations checks the signed and quotient arithmetic independently.
func TestRationalOperations(t *testing.T) {
	values := []Rat{
		MakeRat(0, 1), MakeRat(1, 12), MakeRat(1, 20), MakeRat(1, 3),
		MakeRat(1, 6), MakeRat(-1, 30), MakeRat(2, 15), MakeRat(-1, 15),
		SumRho(3, 5), SumMu(3, 5), SumRho(4, 5), SumMu(4, 5),
	}
	var a, b, want, got big.Rat
	for _, x := range values {
		for _, y := range values {
			a.SetFrac64(x.num, x.den)
			b.SetFrac64(y.num, y.den)
			for op := 0; op < 4; op++ {
				var z Rat
				switch op {
				case 0:
					z = x.Add(y)
					want.Add(&a, &b)
				case 1:
					z = x.Sub(y)
					want.Sub(&a, &b)
				case 2:
					z = x.Mul(y)
					want.Mul(&a, &b)
				case 3:
					if y.num == 0 {
						continue
					}
					z = x.Div(y)
					want.Quo(&a, &b)
				}
				got.SetFrac64(z.num, z.den)
				if got.Cmp(&want) != 0 {
					t.Fatalf("op=%d x=%v y=%v got=%s want=%s", op, x, y, &got, &want)
				}
			}
			if x.Eq(y) != (a.Cmp(&b) == 0) || x.Le(y) != (a.Cmp(&b) <= 0) ||
				x.Lt(y) != (a.Cmp(&b) < 0) {
				t.Fatalf("comparison x=%v y=%v", x, y)
			}
		}
	}
}

// MatchesUpperReference rejects a predicate when any observed answer is wrong.
func MatchesUpperReference(predicate func(uint64) bool) bool {
	var c Cache
	c.Init()
	for n := uint64(2); n <= GridMax; n++ {
		if predicate(n) != c.ReferenceFlags(n)[1] {
			return false
		}
	}
	return true
}

// TestNegativeControls prevents constant answers from passing the upper-bound oracle.
func TestNegativeControls(t *testing.T) {
	if !MatchesUpperReference(MuLeFourRho) {
		t.Fatal("actual predicate does not match the exact reference")
	}
	if MatchesUpperReference(func(uint64) bool { return true }) {
		t.Fatal("always-true predicate passed despite the n=2 counterexample")
	}
	if MatchesUpperReference(func(uint64) bool { return false }) {
		t.Fatal("always-false predicate passed despite equality at n=3")
	}
}

// TestRangeGuards ensures no unchecked machine input reaches a product.
func TestRangeGuards(t *testing.T) {
	predicates := []func(uint64) bool{
		TwoRhoLeMu, MuLeFourRho, RatioAgrees, RatioAtLeastTwo, RatioAtMostFour, MuStep,
	}
	for _, n := range []uint64{0, 1, GridMax + 1, math.MaxUint64} {
		for _, p := range predicates {
			if p(n) {
				t.Fatalf("comparison accepted out-of-range n=%d", n)
			}
		}
	}
	for _, n := range []uint64{0, GridMax + 1, math.MaxUint64} {
		if RhoStep(n) || RhoDen(n) != 0 || MuDen(n) != 0 {
			t.Fatalf("denominator or telescope accepted out-of-range n=%d", n)
		}
	}
}

// TestFiniteGrid pins the certificate size, while TestReferenceGrid checks its meaning.
func TestFiniteGrid(t *testing.T) {
	ok, count := RunAll()
	want := int(GridMax-GridMin+1)*5 + int(GridMax) + int(GridMax-1) + 24
	if !ok || count != want {
		t.Fatalf("ok=%v count=%d want=%d", ok, count, want)
	}
}

// TestNoGridAllocations verifies that the certificate reuses stack witnesses.
func TestNoGridAllocations(t *testing.T) {
	if n := testing.AllocsPerRun(5, func() { RunAll() }); n != 0 {
		t.Fatalf("certificate allocations=%g", n)
	}
}
