// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestHandOffset locks the offset sum to integers computed from the recurrence,
// including q=-2 at time 2, where the sum is -1 rather than the repunit 3.
func TestHandOffset(t *testing.T) {
	neg := []int64{0, 1, -1, 3, -5, 11, -21, 43, -85}
	for j, want := range neg {
		if trapSum(-2, j) != want {
			t.Fatalf("trapSum(-2, %d)=%d, want %d", j, trapSum(-2, j), want)
		}
	}
	if trapSum(-2, 2) != -1 {
		t.Fatal("TrapSum(-2, 2) is not -1")
	}
	signed := (powInt(-2, 2) - 1) / ((-2) - 1)
	if signed != -1 || trapSum(-2, 2) != signed {
		t.Fatal("signed quotient at q=-2, j=2 is not the offset sum")
	}
	if positiveRepunitEqualsAbs(-2, 2) {
		t.Fatal("absolute value matched the positive repunit")
	}
	pos := []int64{0, 1, 3, 7, 15, 31, 63, 127, 255}
	for j, want := range pos {
		if trapSum(2, j) != want {
			t.Fatalf("trapSum(2, %d)=%d, want %d", j, trapSum(2, j), want)
		}
	}
}

// TestRejectsConstantTrue fails if either predicate is replaced by true.
func TestRejectsConstantTrue(t *testing.T) {
	if PositiveClosedFormHolds(-2, 2) || PositiveClosedFormHolds(1, 4) ||
		PositiveClosedFormHolds(0, 3) {
		t.Fatal("positive closed form accepted a multiplier below 2")
	}
	if GeometricAbsHolds(-1, 4) || GeometricAbsHolds(0, 2) ||
		GeometricAbsHolds(1, 5) {
		t.Fatal("absolute bound accepted |q| below 2")
	}
	if !PositiveClosedFormHolds(2, 2) || !PositiveClosedFormHolds(6, 8) {
		t.Fatal("positive closed form rejected a multiplier at least 2")
	}
	if !GeometricAbsHolds(-2, 2) || !GeometricAbsHolds(-6, 8) ||
		!GeometricAbsHolds(3, 4) {
		t.Fatal("absolute bound rejected |q| at least 2")
	}
}

// TestGridAgrees checks the positive quotient only for q ≥ 2 and the absolute
// bound for every |q| ≥ 2 on the printed rectangle. It does not extend the
// claim beyond that rectangle.
func TestGridAgrees(t *testing.T) {
	var checks uint64
	for q := int64(gridQMin); q <= gridQMax; q++ {
		for j := 0; j <= gridMaxJ; j++ {
			sum := trapSum(q, j)
			if q >= 2 {
				pow := powInt(q, j)
				num := pow - 1
				den := q - 1
				if num%den != 0 || sum != num/den || (q-1)*sum != num || sum < 0 {
					t.Fatalf("positive quotient q=%d j=%d sum=%d", q, j, sum)
				}
				if !PositiveClosedFormHolds(q, j) {
					t.Fatalf("predicate refused q=%d j=%d", q, j)
				}
				checks++
			} else if PositiveClosedFormHolds(q, j) {
				t.Fatalf("predicate accepted q=%d j=%d", q, j)
			}
			r := abs64(q)
			if r >= 2 {
				if (r-1)*abs64(sum) > powInt(r, j)-1 {
					t.Fatalf("absolute bound q=%d j=%d sum=%d", q, j, sum)
				}
				if !GeometricAbsHolds(q, j) {
					t.Fatalf("absolute predicate refused q=%d j=%d", q, j)
				}
				checks++
			} else if GeometricAbsHolds(q, j) {
				t.Fatalf("absolute predicate accepted q=%d j=%d", q, j)
			}
		}
	}
	if checks == 0 {
		t.Fatal("grid performed no comparisons")
	}
}
