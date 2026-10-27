// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestSignedProductBoundary rejects the exceptional signed multiplication in either order.
func TestSignedProductBoundary(t *testing.T) {
	const minInt64 = -1 << 63
	if _, ok := MulOK(-1, minInt64); ok {
		t.Fatal("-MinInt64 was accepted as an int64")
	}
	if _, ok := MulOK(minInt64, -1); ok {
		t.Fatal("MinInt64 times -1 was accepted as an int64")
	}
	w := NewWorkspace()
	if !w.Load(-1) {
		t.Fatal("multiplier -1 did not load")
	}
	if _, ok := w.State(0, minInt64, 1); ok {
		t.Fatal("an unrepresentable affine state was accepted")
	}
}

// ExpectUnitHit is the independent multiplier-one criterion for |d|=2:
// an even seed hits at time 0, and an odd seed hits at time 1 exactly
// when the offset is odd. Replacing the scanned predicate by true would
// count every seed and disagree with this count.
func ExpectUnitHit(c, n int64) bool {
	if n%2 == 0 {
		return true
	}
	return c%2 != 0
}

// TestFirstHitRejectsConstantTrue fails if IsFirstHit is replaced by true.
func TestFirstHitRejectsConstantTrue(t *testing.T) {
	w := NewWorkspace()
	if IsFirstHit(w, 1, 0, 2, 1, 0) {
		t.Fatal("q=1,c=0,d=2 reported a hit of seed 1 at time 0")
	}
	if IsFirstHit(w, 1, 0, 2, 1, 1) {
		t.Fatal("q=1,c=0,d=2 reported a hit of seed 1 at time 1")
	}
	if !IsFirstHit(w, 1, 0, 2, 2, 0) {
		t.Fatal("q=1,c=0,d=2 missed the time-zero hit of seed 2")
	}
	if IsFirstHit(w, 1, 1, 2, 1, 0) {
		t.Fatal("q=1,c=1,d=2 reported a time-zero hit of seed 1")
	}
	if !IsFirstHit(w, 1, 1, 2, 1, 1) {
		t.Fatal("q=1,c=1,d=2 missed the time-one hit of seed 1")
	}
}

// TestOddTranslationMisses fails if the hit predicate is replaced by true.
// The state is 2^(j+1)-1, which is odd.
func TestOddTranslationMisses(t *testing.T) {
	w := NewWorkspace()
	for j := 0; j < scanHorizon; j++ {
		if IsFirstHit(w, 2, 1, 2, 1, j) {
			t.Fatalf("odd translation reported a hit at time %d", j)
		}
		state, ok := w.State(1, 1, j)
		if !ok {
			t.Fatalf("state overflow at time %d", j)
		}
		pow := int64(1)
		for i := 0; i < j+1; i++ {
			pow *= 2
		}
		if state != pow-1 {
			t.Fatalf("state %d, expected %d", state, pow-1)
		}
		if state%2 == 0 {
			t.Fatalf("state %d was even", state)
		}
	}
}

// TestPureBoundRejectsSeedOne fails if PureBoundOK is replaced by true.
func TestPureBoundRejectsSeedOne(t *testing.T) {
	if PureBoundOK(2, 1) || PureBoundOK(-2, 1) {
		t.Fatal("pure division accepted the seed 1")
	}
	if !PureBoundOK(2, 2) || !PureBoundOK(-2, -4) || !PureBoundOK(2, -6) {
		t.Fatal("pure division rejected a divisible seed")
	}
	if !PureBoundOK(2, 0) {
		t.Fatal("pure division rejected 0")
	}
}

// TestGridAgreesWithClosedCriterion checks the printed sweep against the
// independent parity criterion. A constant-true hit predicate disagrees.
func TestGridAgreesWithClosedCriterion(t *testing.T) {
	got := Sweep(NewCache())
	if got.Failures != 0 {
		t.Fatalf("sweep failures %d", got.Failures)
	}
	var wantHits uint64
	var wantMiss uint64
	for c := offsetMin; c <= offsetMax; c++ {
		for n := seedMin; n <= seedMax; n++ {
			// Both divisors ±2 induce the same divisibility.
			if ExpectUnitHit(c, n) {
				wantHits += 2
			} else {
				wantMiss += 2
			}
		}
	}
	if got.Hits != wantHits || got.Misses != wantMiss {
		t.Fatalf("hits %d want %d, misses %d want %d",
			got.Hits, wantHits, got.Misses, wantMiss)
	}
	if got.Hits+got.Misses == got.Hits {
		t.Fatal("every grid seed was counted as a hit")
	}
	if got.Checks == 0 {
		t.Fatal("the sweep recorded no checks")
	}
}
