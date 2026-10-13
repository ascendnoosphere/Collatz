// Copyright (c) 2026 ascendnoosphere
// SPDX-License-Identifier: CC-BY-4.0

package main

import "testing"

// alwaysTrue ignores its arguments.
func alwaysTrue(uint64, uint64, uint64, uint64) bool {
	return true
}

// TestDisplayedCells checks the five cells and the comparison count.
func TestDisplayedCells(t *testing.T) {
	cache := DisplayedCache()
	cells := cache.Cells[:]
	cells = cells[:len(cells)]
	var i int
	for i = 0; i < len(cells); i++ {
		cell := cells[i]
		if !IdentityHolds(cell.Q, cell.K, cell.C, cell.D) {
			t.Fatalf("cell %d fails the identity", i)
		}
	}
	totals := CheckDisplayed(cache)
	if totals.Failures != 0 || totals.Checks != displayedChecks {
		t.Fatalf("checks %d failures %d", totals.Checks, totals.Failures)
	}
}

// TestConstantTruePredicateIsRejected separates the identity from a trivial predicate.
func TestConstantTruePredicateIsRejected(t *testing.T) {
	const q, k, c, D uint64 = 2, 2, 1, 5
	if alwaysTrue(q, k, c, D) == IdentityHolds(q, k, c, D) {
		t.Fatal("a constantly true predicate was not rejected")
	}
}

// TestNonDivisorIsRejected checks that D=5 is not the repunit sum G_2(2)=3.
func TestNonDivisorIsRejected(t *testing.T) {
	sum, ok := RepunitSum(2, 2)
	if !ok || sum != 3 {
		t.Fatalf("sum %d ok %v", sum, ok)
	}
	if IdentityHolds(2, 2, 1, 5) {
		t.Fatal("modulus 5 was accepted for q=2 and k=2")
	}
}

// TestRepunitValues checks the five displayed sums and powers directly.
func TestRepunitValues(t *testing.T) {
	type row struct {
		q   uint64
		k   uint64
		sum uint64
		pow uint64
	}
	rows := []row{
		{q: 2, k: 2, sum: 3, pow: 4},
		{q: 2, k: 3, sum: 7, pow: 8},
		{q: 2, k: 4, sum: 15, pow: 16},
		{q: 3, k: 2, sum: 4, pow: 9},
		{q: 3, k: 3, sum: 13, pow: 27},
	}
	rows = rows[:len(rows)]
	var i int
	for i = 0; i < len(rows); i++ {
		got, ok := RepunitSum(rows[i].q, rows[i].k)
		if !ok || got != rows[i].sum {
			t.Fatalf("row %d sum %d", i, got)
		}
		pow, pok := Pow(rows[i].q, rows[i].k)
		if !pok || pow != rows[i].pow {
			t.Fatalf("row %d power %d", i, pow)
		}
		sumOK, geomOK, dvdOK, modOK, coprimeOK, _, _ := DivisorFacts(
			rows[i].q, rows[i].k, rows[i].sum)
		if !(sumOK && geomOK && dvdOK && modOK && coprimeOK) {
			t.Fatalf("row %d facts failed", i)
		}
	}
}
