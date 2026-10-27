// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// ConstantTrue accepts every pair. The equation does not.
func ConstantTrue(uint64, uint) bool {
	return true
}

// TestDisplayedPairs checks the five displayed solutions.
func TestDisplayedPairs(t *testing.T) {
	w := NewWorkspace()
	pairs := DisplayedNagellPairs()
	if len(pairs) != 5 {
		t.Fatalf("displayed count %d", len(pairs))
	}
	for _, p := range pairs {
		if !SatisfiesNagell(w, p.X, p.N) {
			t.Fatalf("pair (%d, %d) failed", p.X, p.N)
		}
	}
}

// TestRejectsConstantTrue fails when the predicate accepts a control pair.
// The constantly true predicate accepts every control pair.
func TestRejectsConstantTrue(t *testing.T) {
	w := NewWorkspace()
	controls := ControlNagellPairs()
	if len(controls) == 0 {
		t.Fatal("control grid is empty")
	}
	separated := false
	for _, p := range controls {
		got := SatisfiesNagell(w, p.X, p.N)
		if got {
			t.Fatalf("control (%d, %d) satisfied the equation", p.X, p.N)
		}
		if ConstantTrue(p.X, p.N) && !got {
			separated = true
		}
	}
	if !separated {
		t.Fatal("predicate agreed with the constantly true predicate")
	}
}

// TestGridCount checks every displayed pair and every control pair.
func TestGridCount(t *testing.T) {
	w := NewWorkspace()
	count, err := RunGrid(w)
	if err != nil {
		t.Fatal(err)
	}
	want := len(DisplayedNagellPairs()) + len(ControlNagellPairs())
	if count != want {
		t.Fatalf("check count %d, want %d", count, want)
	}
	if count != 12 {
		t.Fatalf("check count %d", count)
	}
}
