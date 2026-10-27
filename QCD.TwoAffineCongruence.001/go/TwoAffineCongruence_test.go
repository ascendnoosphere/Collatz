// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// ConstantTrue accepts every lane. The congruence does not.
func ConstantTrue(Lane) bool {
	return true
}

// TestPositiveLanes checks the five integral lanes, including the unit equality.
func TestPositiveLanes(t *testing.T) {
	w := NewWorkspace()
	lanes := PositiveLanes()
	if len(lanes) != 5 {
		t.Fatalf("positive count %d", len(lanes))
	}
	sawEqual := false
	sawOddUnequal := false
	for _, item := range lanes {
		if err := w.CheckPositive(item); err != nil {
			t.Fatal(err)
		}
		if item.N == item.Y {
			sawEqual = true
			if item.Lane.K%2 != 0 {
				t.Fatalf("equal lane has odd length %d", item.Lane.K)
			}
		}
		if item.Lane.K%2 == 1 && item.N != item.Y {
			sawOddUnequal = true
		}
	}
	if !sawEqual {
		t.Fatal("grid omitted the unit equality")
	}
	if !sawOddUnequal {
		t.Fatal("grid omitted an odd length with unequal quotients")
	}
}

// TestControlsFail checks that each control congruence fails.
func TestControlsFail(t *testing.T) {
	w := NewWorkspace()
	lanes := ControlLanes()
	if len(lanes) != 5 {
		t.Fatalf("control count %d", len(lanes))
	}
	for _, lane := range lanes {
		if err := w.CheckControl(lane); err != nil {
			t.Fatal(err)
		}
	}
}

// TestBoundaryPartnerEven checks that the zero exponent can produce an even partner.
func TestBoundaryPartnerEven(t *testing.T) {
	w := NewWorkspace()
	if err := w.CheckBoundary(BoundaryLane()); err != nil {
		t.Fatal(err)
	}
}

// TestRejectsConstantTrue fails when the predicate accepts a control lane.
// The constantly true predicate accepts every control lane.
func TestRejectsConstantTrue(t *testing.T) {
	w := NewWorkspace()
	controls := ControlLanes()
	if len(controls) == 0 {
		t.Fatal("control grid is empty")
	}
	separated := false
	for _, lane := range controls {
		delta, ok := w.Delta(lane.K, lane.Q)
		if !ok {
			t.Fatal("control power missing")
		}
		got := w.Congruent(delta, lane.Q, lane.A)
		if got {
			t.Fatalf("control (%d, %d, %d) satisfied the congruence", lane.K, lane.Q, lane.A)
		}
		if ConstantTrue(lane) && !got {
			separated = true
		}
	}
	if !separated {
		t.Fatal("predicate agreed with the constantly true predicate")
	}
}

// TestGridCount checks every displayed lane and records the check count.
func TestGridCount(t *testing.T) {
	w := NewWorkspace()
	count, err := w.RunGrid()
	if err != nil {
		t.Fatal(err)
	}
	want := len(PositiveLanes()) + len(ControlLanes()) + 1
	if count != want {
		t.Fatalf("check count %d, want %d", count, want)
	}
	if count != 11 {
		t.Fatalf("check count %d", count)
	}
}
