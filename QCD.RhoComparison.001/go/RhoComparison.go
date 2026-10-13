// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"fmt"
	"os"
)

const (
	// GridMin is the first integer covered by both comparison bounds.
	GridMin uint64 = 3
	// GridMax bounds every machine-integer check; no product exceeds 2^38.
	GridMax uint64 = 4096
	// WitnessMax bounds the exact rational partial-sum witnesses.
	WitnessMax uint64 = 8
)

// Rat stores a reduced rational with positive denominator.
// It is used only for the explicitly bounded witnesses, not arbitrary inputs.
type Rat struct {
	num int64
	den int64
}

// Gcd cancels common factors in the bounded rational witnesses.
func Gcd(a, b int64) int64 {
	if a < 0 {
		a = -a
	}
	if b < 0 {
		b = -b
	}
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// MakeRat normalizes a witness and rejects a zero denominator.
func MakeRat(n, d int64) Rat {
	if d == 0 {
		panic("zero rational denominator")
	}
	if d < 0 {
		n, d = -n, -d
	}
	g := Gcd(n, d)
	return Rat{num: n / g, den: d / g}
}

// Add uses denominator cancellation before forming a sum.
func (a Rat) Add(b Rat) Rat {
	g := Gcd(a.den, b.den)
	return MakeRat(a.num*(b.den/g)+b.num*(a.den/g), (a.den/g)*b.den)
}

// Sub forms the difference of two bounded witnesses.
func (a Rat) Sub(b Rat) Rat {
	return a.Add(MakeRat(-b.num, b.den))
}

// Mul cross-cancels before multiplying bounded witnesses.
func (a Rat) Mul(b Rat) Rat {
	g := Gcd(a.num, b.den)
	h := Gcd(b.num, a.den)
	return MakeRat((a.num/g)*(b.num/h), (a.den/h)*(b.den/g))
}

// Div rejects division by zero and cross-cancels the nonzero divisor.
func (a Rat) Div(b Rat) Rat {
	if b.num == 0 {
		panic("zero rational divisor")
	}
	return a.Mul(MakeRat(b.den, b.num))
}

// Eq compares two bounded witnesses by their cross products.
func (a Rat) Eq(b Rat) bool {
	return a.num*b.den == b.num*a.den
}

// Le compares bounded witnesses with their positive denominators.
func (a Rat) Le(b Rat) bool {
	return a.num*b.den <= b.num*a.den
}

// Lt performs the strict comparison needed by the signed counterexamples.
func (a Rat) Lt(b Rat) bool {
	return a.num*b.den < b.num*a.den
}

// RhoDen returns n(n+1), or zero outside the certified machine range.
func RhoDen(n uint64) uint64 {
	if n < 1 || n > GridMax {
		return 0
	}
	return n * (n + 1)
}

// MuDen returns n(n-1), or zero outside the certified machine range.
func MuDen(n uint64) uint64 {
	if n < 2 || n > GridMax {
		return 0
	}
	return n * (n - 1)
}

// RhoRat returns rho(n) only within the small rational witness range.
func RhoRat(n uint64) Rat {
	if n < 1 || n > WitnessMax {
		panic("rho witness outside range")
	}
	return MakeRat(1, int64(RhoDen(n)))
}

// MuRat returns mu(n) only within the small rational witness range.
func MuRat(n uint64) Rat {
	if n < 2 || n > WitnessMax {
		panic("mu witness outside range")
	}
	return MakeRat(2, int64(MuDen(n)))
}

// TwoRhoLeMu evaluates the cleared lower bound, including the endpoint n=2.
func TwoRhoLeMu(n uint64) bool {
	if n < 2 || n > GridMax {
		return false
	}
	return 2*MuDen(n) <= 2*RhoDen(n)
}

// MuLeFourRho evaluates the upper bound; it is false by arithmetic at n=2.
func MuLeFourRho(n uint64) bool {
	if n < 2 || n > GridMax {
		return false
	}
	return 2*RhoDen(n) <= 4*MuDen(n)
}

// RatioAgrees checks the ratio identity after clearing its positive denominators.
func RatioAgrees(n uint64) bool {
	if n < 2 || n > GridMax {
		return false
	}
	return 2*RhoDen(n)*(n-1) == 2*(n+1)*MuDen(n)
}

// RatioAtLeastTwo evaluates the cleared scalar lower bound.
func RatioAtLeastTwo(n uint64) bool {
	if n < 2 || n > GridMax {
		return false
	}
	return 2*(n-1) <= 2*(n+1)
}

// RatioAtMostFour evaluates the cleared scalar upper bound, including n=2.
func RatioAtMostFour(n uint64) bool {
	if n < 2 || n > GridMax {
		return false
	}
	return 2*(n+1) <= 4*(n-1)
}

// RhoStep clears the reciprocal difference over n(n+1).
func RhoStep(n uint64) bool {
	if n < 1 || n > GridMax {
		return false
	}
	return RhoDen(n)/n-RhoDen(n)/(n+1) == 1
}

// MuStep clears the reciprocal difference over n(n-1).
func MuStep(n uint64) bool {
	if n < 2 || n > GridMax {
		return false
	}
	return 2*(MuDen(n)/(n-1))-2*(MuDen(n)/n) == 2
}

// SumRho sums a window in [1,8]; an empty window has sum zero.
func SumRho(lo, hi uint64) Rat {
	if lo < 1 || lo > WitnessMax+1 || hi > WitnessMax {
		panic("rho sum outside range")
	}
	s := MakeRat(0, 1)
	for n := lo; n <= hi; n++ {
		s = s.Add(RhoRat(n))
	}
	return s
}

// SumMu sums a window in [2,8]; an empty window has sum zero.
func SumMu(lo, hi uint64) Rat {
	if lo < 2 || lo > WitnessMax+1 || hi > WitnessMax {
		panic("mu sum outside range")
	}
	s := MakeRat(0, 1)
	for n := lo; n <= hi; n++ {
		s = s.Add(MuRat(n))
	}
	return s
}

// RhoPartialAgrees includes the empty sum at R=0.
func RhoPartialAgrees(r uint64) bool {
	if r > WitnessMax {
		return false
	}
	return SumRho(1, r).Eq(MakeRat(int64(r), int64(r)+1))
}

// MuPartialAgrees includes the empty sum at R=2.
func MuPartialAgrees(r uint64) bool {
	if r < 2 || r > WitnessMax {
		return false
	}
	return SumMu(3, r).Eq(MakeRat(int64(r)-2, int64(r)))
}

// Witnesses checks endpoints, partial sums, windows, signs, and mass quotients.
func Witnesses() (bool, int) {
	ok := true
	count := 0
	for r := uint64(0); r <= WitnessMax; r++ {
		ok = RhoPartialAgrees(r) && ok
		count++
	}
	for r := uint64(2); r <= WitnessMax; r++ {
		ok = MuPartialAgrees(r) && ok
		count++
	}
	// Each window is computed by summing, then compared with the telescoped value.
	ok = SumRho(4, 7).Eq(MakeRat(1, 4).Sub(MakeRat(1, 8))) && ok
	ok = SumMu(4, 7).Eq(MakeRat(2, 3).Sub(MakeRat(2, 7))) && ok
	ok = MakeRat(4, 1).Mul(RhoRat(2)).Lt(MuRat(2)) && ok
	ok = MakeRat(4, 1).Mul(RhoRat(3)).Eq(MuRat(3)) && ok
	// The two sign choices refute the upper and lower signed extensions.
	ok = MakeRat(4, 1).Mul(RhoRat(3).Sub(RhoRat(4))).Lt(
		MuRat(3).Sub(MuRat(4))) && ok
	ok = MuRat(4).Sub(MuRat(3)).Lt(
		MakeRat(2, 1).Mul(RhoRat(4).Sub(RhoRat(3)))) && ok
	r := SumRho(3, 5)
	m := SumMu(3, 5)
	ok = MakeRat(2, 1).Mul(r).Le(m) && m.Le(MakeRat(4, 1).Mul(r)) && ok
	pr := RhoRat(3).Div(SumRho(4, 5))
	pm := MuRat(3).Div(SumMu(4, 5))
	ok = pr.Div(MakeRat(2, 1)).Le(pm) && pm.Le(MakeRat(2, 1).Mul(pr)) && ok
	return ok, count + 8
}

// RunAll executes every grid check even after a failure; the grid is not the theorem.
func RunAll() (bool, int) {
	ok := true
	count := 0
	for n := GridMin; n <= GridMax; n++ {
		ok = TwoRhoLeMu(n) && ok
		ok = MuLeFourRho(n) && ok
		ok = RatioAgrees(n) && ok
		ok = RatioAtLeastTwo(n) && ok
		ok = RatioAtMostFour(n) && ok
		count += 5
	}
	for n := uint64(1); n <= GridMax; n++ {
		ok = RhoStep(n) && ok
		count++
	}
	for n := uint64(2); n <= GridMax; n++ {
		ok = MuStep(n) && ok
		count++
	}
	wok, wcount := Witnesses()
	return wok && ok, count + wcount
}

// main reports the finite checks without extending their scope to all integers.
func main() {
	ok, count := RunAll()
	if !ok {
		fmt.Println("finite arithmetic check failed")
		os.Exit(1)
	}
	fmt.Printf("finite arithmetic checks passed: %d\n", count)
}
