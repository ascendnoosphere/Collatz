// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// referenceSum recomputes the offset sum from the closed form with exact
// big-integer arithmetic, independently of the iteration of TrapSumInt.
func referenceSum(q int64, j int) *big.Int {
	pow := new(big.Int).Exp(big.NewInt(q), big.NewInt(int64(j)), nil)
	if q == 1 {
		return big.NewInt(int64(j))
	}
	num := new(big.Int).Sub(pow, big.NewInt(1))
	den := big.NewInt(q - 1)
	return num.Quo(num, den)
}

// referenceStep applies one raw step with big-integer arithmetic, so it is
// independent of the int64 step of the certificate.
func referenceStep(q, c, D, n int64) *big.Int {
	bigD := big.NewInt(D)
	bigN := big.NewInt(n)
	rem := new(big.Int).Rem(bigN, bigD)
	if rem.Sign() == 0 {
		return new(big.Int).Quo(bigN, bigD)
	}
	out := new(big.Int).Mul(big.NewInt(q), bigN)
	return out.Add(out, big.NewInt(c))
}

// TestTrapSumMatchesReference compares the iterated offset sum with the closed
// form for every multiplier and index of the grid.
func TestTrapSumMatchesReference(t *testing.T) {
	for q := int64(-signedTrapMaxQ); q <= signedTrapMaxQ; q++ {
		for j := 0; j <= signedTrapMaxJ; j++ {
			want := referenceSum(q, j)
			if !want.IsInt64() {
				t.Fatalf("reference sum overflows int64 at q=%d j=%d", q, j)
			}
			if got := TrapSumInt(q, j); got != want.Int64() {
				t.Fatalf("offset sum q=%d j=%d: got %d, want %s", q, j, got, want)
			}
		}
	}
}

// TestStepMatchesReference compares the production step with the big-integer
// reference over signed divisors, signed states and both branches, including
// exact multiples of the divisor and the divisor one.
func TestStepMatchesReference(t *testing.T) {
	divisors := append([]int64{1, -1, 4, -4}, signedDivisorList()...)
	for _, D := range divisors {
		for q := int64(-4); q <= 4; q++ {
			for c := int64(-4); c <= 4; c++ {
				for n := int64(-30); n <= 30; n++ {
					want := referenceStep(q, c, D, n)
					if !want.IsInt64() {
						t.Fatalf("reference step overflows at %d %d %d %d", q, c, D, n)
					}
					if got := SignedStep(q, c, D, n); got != want.Int64() {
						t.Fatalf("step q=%d c=%d D=%d n=%d: got %d, want %s",
							q, c, D, n, got, want)
					}
					multiple := D * int64(n)
					if got := SignedStep(q, c, D, multiple); got != n {
						t.Fatalf("division branch D=%d n=%d: got %d, want %d",
							D, multiple, got, n)
					}
				}
			}
		}
	}
}

// TestResidueStepInRange checks that the residue map returns a legitimate
// representative of the affine residue and never leaves the modulus range.
func TestResidueStepInRange(t *testing.T) {
	for m := int64(2); m <= signedResidueMax; m++ {
		for q := int64(-4); q <= 4; q++ {
			for c := int64(-4); c <= 4; c++ {
				for r := int64(0); r < m; r++ {
					got := ResidueStep(q, c, m, r)
					if got < 0 || got >= m {
						t.Fatalf("residue out of range m=%d q=%d c=%d r=%d: %d",
							m, q, c, r, got)
					}
					if want := Residue(q*r+c, m); got != want {
						t.Fatalf("residue m=%d q=%d c=%d r=%d: got %d, want %d",
							m, q, c, r, got, want)
					}
				}
			}
		}
	}
}

// TestOrbitBranches checks the documented walks: the divisor one fixes every
// state, the zero multiplier reaches the constant offset, the negative unit
// multiplier runs the reflection pair, and an expanding multiplier escapes the
// rounding of the affine branch.
func TestOrbitBranches(t *testing.T) {
	w := NewWorkspace()
	orbit := fillOrbit(w.Orbit, 2, 1, 3, 9)
	want := []int64{9, 3, 1, 3, 1}
	for i, value := range want {
		if orbit[i] != value {
			t.Fatalf("orbit at %d: got %d, want %d", i, orbit[i], value)
		}
	}
	orbit = fillOrbit(w.Orbit, 0, 0, 3, 7)
	if orbit[0] != 7 {
		t.Fatalf("first state of the zero-multiplier walk: got %d", orbit[0])
	}
	for j := 1; j < len(orbit); j++ {
		if orbit[j] != 0 {
			t.Fatalf("zero-multiplier walk at %d: got %d", j, orbit[j])
		}
	}
	orbit = fillOrbit(w.Orbit, -1, 0, 7, 5)
	for j := 0; j < len(orbit); j++ {
		want := int64(5)
		if j%2 == 1 {
			want = -5
		}
		if orbit[j] != want {
			t.Fatalf("reflection walk at %d: got %d, want %d", j, orbit[j], want)
		}
	}
	orbit = fillOrbit(w.Orbit, 2, -4, 3, 25)
	if !divisionFree(orbit, 3) || !escapes(orbit) {
		t.Fatalf("expanding walk of (2,-4,3,25) neither clean nor escaping")
	}
	if orbit[signedHorizon] != 352321540 {
		t.Fatalf("expanding walk at the horizon: got %d", orbit[signedHorizon])
	}
}

// TestSweepTotals pins every slice count and the printed total, and reruns the
// sweeps to require a second zero-failure pass.
func TestSweepTotals(t *testing.T) {
	sum := Totals{}
	sweepTrapSum(&sum)
	if sum.Checks != 1010 || sum.Failures != 0 {
		t.Fatalf("offset sums: %d checks, %d failures", sum.Checks, sum.Failures)
	}
	itinerary := runMultiplierSweep(sweepItineraryQ)
	if itinerary.Checks != 99872 || itinerary.Failures != 0 {
		t.Fatalf("itinerary: %d checks, %d failures", itinerary.Checks, itinerary.Failures)
	}
	classes := runMultiplierSweep(classificationQ)
	if classes.Checks != 18464 || classes.Failures != 0 {
		t.Fatalf("classification: %d checks, %d failures", classes.Checks, classes.Failures)
	}
	residues := Totals{}
	sweepResidues(&residues)
	if residues.Checks != 6237 || residues.Failures != 0 {
		t.Fatalf("residues: %d checks, %d failures", residues.Checks, residues.Failures)
	}
	controls := Totals{}
	sweepControls(NewWorkspace(), &controls)
	if controls.Checks != 125 || controls.Failures != 0 {
		t.Fatalf("controls: %d checks, %d failures", controls.Checks, controls.Failures)
	}
	total := sum.Checks + itinerary.Checks + classes.Checks + residues.Checks + controls.Checks
	if total != 125708 {
		t.Fatalf("printed total: got %d, want 125708", total)
	}
	repeat := Totals{}
	sweepTrapSum(&repeat)
	sweepResidues(&repeat)
	sweepControls(NewWorkspace(), &repeat)
	if repeat.Failures != 0 {
		t.Fatalf("second pass reported %d failures", repeat.Failures)
	}
}

// TestWarmedAllocation requires the orbit walk to allocate nothing once the
// shared buffer has grown to the horizon width.
func TestWarmedAllocation(t *testing.T) {
	w := NewWorkspace()
	walk := func() {
		orbit := fillOrbit(w.Orbit, 2, 1, 5, 11)
		if len(orbit) != signedHorizon+1 {
			t.Fatalf("walk length %d", len(orbit))
		}
	}
	walk()
	allocs := testing.AllocsPerRun(100, walk)
	if allocs != 0 {
		t.Fatalf("orbit walk allocated %v values per run", allocs)
	}
}

// TestDocumentedRanges checks the range claims of the certificate: the offset
// sums of the grid stay inside int64, the orbit sweep stays well inside it,
// and the escape bound is reached by the expanding walks of the grid.
func TestDocumentedRanges(t *testing.T) {
	limit := new(big.Int).Lsh(big.NewInt(1), 63)
	worst := new(big.Int).Exp(big.NewInt(signedTrapMaxQ), big.NewInt(signedTrapMaxJ), nil)
	if worst.Cmp(limit) >= 0 {
		t.Fatalf("power bound %s reached the int64 limit", worst)
	}
	orbitBound := new(big.Int).Exp(big.NewInt(signedOffsetMax), big.NewInt(signedHorizon), nil)
	orbitBound.Mul(orbitBound, big.NewInt(30))
	if orbitBound.Cmp(new(big.Int).Lsh(big.NewInt(1), 59)) >= 0 {
		t.Fatalf("orbit bound %s reached the documented range", orbitBound)
	}
	w := NewWorkspace()
	orbit := fillOrbit(w.Orbit, 2, -4, -5, -1)
	if !divisionFree(orbit, 5) || !escapes(orbit) {
		t.Fatalf("expanding walk of (2,-4,-5,-1) neither clean nor escaping")
	}
}
