// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// compared is one integer comparison from exact arithmetic.
type compared struct {
	left  int64
	right int64
	ok    bool
}

// asInt64 returns z as an int64, or fails if it does not fit.
func asInt64(t *testing.T, z *big.Int) int64 {
	t.Helper()
	if !z.IsInt64() {
		t.Fatalf("value %s does not fit", z)
	}
	return z.Int64()
}

// exactPairs builds the checker's comparisons from math/big, in the same
// order, and counts quotient-contraction comparisons.
func exactPairs(t *testing.T, A, B, m int64) ([]compared, int) {
	t.Helper()
	gap := big.NewInt(m - A)
	nBig := new(big.Int).Quo(big.NewInt(B), new(big.Int).Set(gap))
	N := asInt64(t, nBig)
	if CoreRadiusInt(A, B, m) != N {
		t.Fatalf("radius A=%d B=%d m=%d", A, B, m)
	}
	if N+1 > coreMaxN {
		t.Fatalf("no exterior point for N=%d", N)
	}
	out := make([]compared, 0, 96)
	roomR := new(big.Int).Mul(new(big.Int).Set(gap), big.NewInt(N+1))
	out = append(out, compared{B, asInt64(t, roomR), big.NewInt(B).Cmp(roomR) < 0})
	contractions := 0
	for n := int64(0); n <= coreMaxN; n++ {
		left := new(big.Int).Mul(big.NewInt(A), big.NewInt(n))
		left.Add(left, big.NewInt(B))
		var right *big.Int
		if n >= N+1 {
			right = new(big.Int).Mul(big.NewInt(m), big.NewInt(n))
		} else {
			right = new(big.Int).Mul(big.NewInt(m), big.NewInt(N+1))
		}
		ok := left.Cmp(right) < 0
		if !ok {
			t.Fatalf("natural comparison false at %d,%d,%d,%d", A, B, m, n)
		}
		out = append(out, compared{asInt64(t, left), asInt64(t, right), ok})
	}
	for n := int64(-coreMapMax); n <= coreMapMax; n++ {
		mag := n
		if mag < 0 {
			mag = -mag
		}
		sum := new(big.Int).Mul(big.NewInt(A), big.NewInt(mag))
		sum.Add(sum, big.NewInt(B))
		hmag := new(big.Int).Quo(new(big.Int).Set(sum), big.NewInt(m))
		prod := new(big.Int).Mul(big.NewInt(m), new(big.Int).Set(hmag))
		if prod.Cmp(sum) > 0 {
			t.Fatalf("division identity failed at %d", n)
		}
		out = append(out, compared{
			asInt64(t, prod), asInt64(t, sum), prod.Cmp(sum) <= 0,
		})
		if mag >= N+1 {
			ok := hmag.Cmp(big.NewInt(mag)) < 0
			if !ok {
				t.Fatalf("quotient contraction false at %d,%d,%d,%d", A, B, m, n)
			}
			out = append(out, compared{asInt64(t, hmag), mag, ok})
			contractions++
		} else {
			ok := hmag.Cmp(big.NewInt(N)) <= 0
			if !ok {
				t.Fatalf("quotient shell false at %d,%d,%d,%d", A, B, m, n)
			}
			out = append(out, compared{asInt64(t, hmag), N, ok})
		}
	}
	return out, contractions
}

// TestGridMatchesReference compares every checker pair and truth value with
// math/big, and requires both an interior and an exterior natural point.
func TestGridMatchesReference(t *testing.T) {
	vals := make([][2]int64, 0, 96)
	oks := make([]bool, 0, 96)
	for A := int64(0); A <= coreMaxA; A++ {
		for gap := int64(1); gap <= coreMaxGap; gap++ {
			m := A + gap
			for B := int64(0); B <= coreMaxB; B++ {
				want, contractions := exactPairs(t, A, B, m)
				N := CoreRadiusInt(A, B, m)
				if N >= 12 && contractions != 0 {
					t.Fatalf("contraction sampled at N=%d", N)
				}
				if N <= 11 && contractions == 0 {
					t.Fatalf("contraction missing at N=%d", N)
				}
				vals = vals[:0]
				oks = oks[:0]
				sink := Totals{Values: &vals, Bools: &oks}
				checkTriple(A, B, m, &sink)
				if sink.Failures != 0 || len(vals) != len(want) || len(oks) != len(want) {
					t.Fatalf("checker %d,%d,%d failures %d",
						A, B, m, sink.Failures)
				}
				for i := range want {
					if vals[i][0] != want[i].left || vals[i][1] != want[i].right ||
						oks[i] != want[i].ok {
						t.Fatalf("pair %d at %d,%d,%d", i, A, B, m)
					}
				}
			}
		}
	}
}

// TestControls checks the documented boundary arithmetic.
func TestControls(t *testing.T) {
	if CoreRadiusInt(2, 7, 3) != 7 {
		t.Fatal("radius")
	}
	if 2*8+7 >= 3*8 || 2*7+7 >= 3*8 {
		t.Fatal("boundary")
	}
	if (2*8+7)/3 != 7 || (2*absInt(-8)+7)/3 != 7 {
		t.Fatal("quotient")
	}
	if 2*7+7 < 3*7 {
		t.Fatal("equality is not strict descent")
	}
	if 5 >= 1*(CoreRadiusInt(0, 5, 1)+1) {
		t.Fatal("zero coefficient")
	}
	if 3*6+5 >= 4*6 {
		t.Fatal("unit gap")
	}
	controls := Totals{}
	SweepControls(&controls)
	if controls.Checks != 8 || controls.Failures != 0 {
		t.Fatalf("controls %+v", controls)
	}
}

// TestSweepCount pins the grid size and requires a clean run.
func TestSweepCount(t *testing.T) {
	triples := uint64(coreMaxA+1) * uint64(coreMaxGap) * uint64(coreMaxB+1)
	nat := triples * uint64(coreMaxN+1)
	maps := triples * uint64(2*coreMapMax+1) * 2
	room := triples
	got := SweepCore()
	if got.Failures != 0 {
		t.Fatalf("failures %d", got.Failures)
	}
	if got.Checks != room+nat+maps {
		t.Fatalf("checks %d want %d", got.Checks, room+nat+maps)
	}
	if got.Checks+8 != 165608 {
		t.Fatalf("total %d", got.Checks+8)
	}
}

// TestCheckAllocations requires the single-triple checker to allocate nothing
// after the testing harness is warm.
func TestCheckAllocations(t *testing.T) {
	var sink Totals
	testing.AllocsPerRun(1, func() { checkTriple(2, 7, 3, &sink) })
	allocs := testing.AllocsPerRun(20, func() { checkTriple(2, 7, 3, &sink) })
	if allocs != 0 {
		t.Fatalf("allocations %v", allocs)
	}
}
