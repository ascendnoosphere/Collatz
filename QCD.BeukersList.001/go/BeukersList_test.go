// Copyright (c) 2026 ascendnoosphere
// SPDX-License-Identifier: CC-BY-4.0

package main

import "testing"

// TestDisplayedPairs checks the seven pairs with big integers.
func TestDisplayedPairs(t *testing.T) {
	work := NewWorkspace()
	for _, p := range displayedPairs {
		if !DisplayedHolds(work, p) {
			t.Fatalf("displayed pair failed: %+v", p)
		}
		if !EquationHolds(p.D, p.X, p.N) {
			t.Fatalf("uint64 pair failed: %+v", p)
		}
	}
}

// TestBoxMatchesDisplayed compares the exponent sweep with the finite lists.
func TestBoxMatchesDisplayed(t *testing.T) {
	sevenTotals, seven := RunBox(7)
	if sevenTotals.Failures != 0 {
		t.Fatalf("D=7 box failures %d", sevenTotals.Failures)
	}
	if !SamePairs(seven, wantSeven) {
		t.Fatalf("D=7 hits %+v", seven)
	}
	twentyTotals, twenty := RunBox(23)
	if twentyTotals.Failures != 0 {
		t.Fatalf("D=23 box failures %d", twentyTotals.Failures)
	}
	if !SamePairs(twenty, wantTwenty) {
		t.Fatalf("D=23 hits %+v", twenty)
	}
}

// TestMersenneGrid checks the parametric identities only for 4<=k<=32.
func TestMersenneGrid(t *testing.T) {
	totals := RunMersenne()
	if totals.Failures != 0 {
		t.Fatalf("mersenne failures %d", totals.Failures)
	}
	span := mersenneMaxK - mersenneMinK + 1
	if totals.Checks != uint64(3*span) {
		t.Fatalf("mersenne checks %d", totals.Checks)
	}
}

// TestConstantlyTruePredicateIsRejected rejects a predicate that ignores the equation.
func TestConstantlyTruePredicateIsRejected(t *testing.T) {
	always := func(uint64, uint64, uint64) bool { return true }
	if CertificateOK(always) {
		t.Fatal("a constantly true predicate was accepted")
	}
}

// TestConstantlyFalsePredicateIsRejected rejects a predicate that misses the displayed pairs.
func TestConstantlyFalsePredicateIsRejected(t *testing.T) {
	never := func(uint64, uint64, uint64) bool { return false }
	if CertificateOK(never) {
		t.Fatal("a constantly false predicate was accepted")
	}
}

// TestEquationRejectsNearMiss checks the four triples adjacent to displayed solutions.
func TestEquationRejectsNearMiss(t *testing.T) {
	if !CertificateOK(EquationHolds) {
		t.Fatal("EquationHolds failed the displayed-or-near-miss certificate")
	}
	for _, p := range nearMisses {
		if EquationHolds(p.D, p.X, p.N) {
			t.Fatalf("near miss accepted: %+v", p)
		}
	}
}

// TestCheckCountMatchesFormula ties the printed counter to the grid size.
func TestCheckCountMatchesFormula(t *testing.T) {
	totals := Certify()
	if totals.Failures != 0 {
		t.Fatalf("failures %d", totals.Failures)
	}
	if totals.Checks != ExpectedChecks() {
		t.Fatalf("checks %d want %d", totals.Checks, ExpectedChecks())
	}
	if totals.Checks != 165 {
		t.Fatalf("checks %d want 165", totals.Checks)
	}
}

// TestPositiveRootBoundaries rejects a zero root, a negative remainder, and a wide exponent.
func TestPositiveRootBoundaries(t *testing.T) {
	for _, tc := range []struct {
		d    uint64
		n    uint64
		root uint64
		ok   bool
	}{
		{8, 3, 0, false},
		{9, 3, 0, false},
		{0, 0, 1, true},
		{7, 4, 3, true},
		{7, 64, 0, false},
	} {
		root, ok := PositiveRoot(tc.d, tc.n)
		if root != tc.root || ok != tc.ok {
			t.Fatalf("D=%d n=%d: got (%d,%v), want (%d,%v)",
				tc.d, tc.n, root, ok, tc.root, tc.ok)
		}
	}
}

// TestIsqrt checks squares, the predecessor of a square, and the 2^32 boundary.
func TestIsqrt(t *testing.T) {
	if IntegerSquareRoot(0) != 0 || IntegerSquareRoot(1) != 1 || IntegerSquareRoot(2) != 1 {
		t.Fatal("small roots")
	}
	if IntegerSquareRoot(181*181) != 181 || IntegerSquareRoot(181*181-1) != 180 {
		t.Fatal("181 boundary")
	}
	hi := uint64(1) << 32
	if IntegerSquareRoot(hi) != 1<<16 || IntegerSquareRoot(hi-1) != (1<<16)-1 {
		t.Fatal("2^32 boundary")
	}
}
