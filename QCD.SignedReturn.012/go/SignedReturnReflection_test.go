// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestStateEqualsRejectsSlack fails if the affine predicate is replaced by true.
func TestStateEqualsRejectsSlack(t *testing.T) {
	w := NewWorkspace()
	// Time 0: power 1, sum 0, state equals the seed.
	w.Prepare(0)
	if w.Pow != 1 || w.Trap != 0 {
		t.Fatalf("time zero power %d sum %d", w.Pow, w.Trap)
	}
	if !StateEquals(w.Pow, w.Trap, 4, -3, -3) {
		t.Fatal("time zero rejected the seed")
	}
	if StateEquals(w.Pow, w.Trap, 4, -3, -2) {
		t.Fatal("time zero accepted a unit slack")
	}
	// Time 1: power -1, sum 1, state equals c-n.
	w.Prepare(1)
	if w.Pow != -1 || w.Trap != 1 {
		t.Fatalf("time one power %d sum %d", w.Pow, w.Trap)
	}
	if !StateEquals(w.Pow, w.Trap, 4, 9, 4-9) {
		t.Fatal("time one rejected c-n")
	}
	if StateEquals(w.Pow, w.Trap, 4, 9, 0) {
		t.Fatal("time one accepted a false value")
	}
	// Time 2 repeats time 0, and time 3 repeats time 1.
	w.Prepare(2)
	if !StateEquals(w.Pow, w.Trap, -2, 5, 5) {
		t.Fatal("time two did not repeat the seed")
	}
	w.Prepare(3)
	if !StateEquals(w.Pow, w.Trap, -2, 5, -2-5) {
		t.Fatal("time three did not repeat c-n")
	}
	if StateEquals(w.Pow, w.Trap, -2, 5, 5) {
		t.Fatal("odd time was treated as even")
	}
}

// TestClausesAndBases checks one witness of each clause, including negatives.
func TestClausesAndBases(t *testing.T) {
	cache := NewCache()
	ps := cache.Pow[:len(cache.Pow)]
	ts := cache.Trap[:len(cache.Trap)]
	// Clause 0: d = 2 divides n = 4. Return 4/2 = 2. Time 1 is not first.
	if ClauseOf(2, 0, 4) != clauseHitZero {
		t.Fatal("divisible seed was not clause zero")
	}
	if !IsFirstHit(ps, ts, 2, 0, 4, 0) {
		t.Fatal("time zero missed a divisible seed")
	}
	if IsFirstHit(ps, ts, 2, 0, 4, 1) {
		t.Fatal("a later time was first after time zero")
	}
	if 2*(4/2) != 4 {
		t.Fatal("time-zero quotient was not exact")
	}
	// Clause 0 with a negative divisor: (-8)/(-4) = 2.
	if ClauseOf(-4, 2, -8) != clauseHitZero {
		t.Fatal("negative divisor rejected a multiple")
	}
	if !IsFirstHit(ps, ts, -4, 2, -8, 0) || IsFirstHit(ps, ts, -4, 2, -8, 2) {
		t.Fatal("negative divisor mishandled the first hit")
	}
	if -4*((-8)/(-4)) != -8 {
		t.Fatal("negative quotient was not exact")
	}
	// Clause 1: d = 2 misses n = 1 and divides c-n = 4. Return 2.
	if ClauseOf(2, 5, 1) != clauseHitOne {
		t.Fatal("reflection hit was not clause one")
	}
	if IsFirstHit(ps, ts, 2, 5, 1, 0) || !IsFirstHit(ps, ts, 2, 5, 1, 1) {
		t.Fatal("clause one did not hit exactly at time one")
	}
	if IsFirstHit(ps, ts, 2, 5, 1, 3) {
		t.Fatal("clause one kept a later odd time as first")
	}
	if 2*((5-1)/2) != 4 {
		t.Fatal("time-one quotient was not exact")
	}
	// Clause 1 with return 0: c-n = 0 is divisible, and the seed is not.
	if ClauseOf(4, 1, 1) != clauseHitOne {
		t.Fatal("zero reflection was not clause one")
	}
	if !IsFirstHit(ps, ts, 4, 1, 1, 1) || 4*((1-1)/4) != 0 {
		t.Fatal("zero return was rejected")
	}
	// Clause 1 with a negative reflection: c-n = -5, return -1.
	if ClauseOf(5, -3, 2) != clauseHitOne {
		t.Fatal("negative reflection was not clause one")
	}
	if 5*((-3-2)/5) != -5 {
		t.Fatal("negative reflection quotient was not exact")
	}
	// Clause 2: d = 2 divides neither 1 nor -1. No time is a first hit.
	if ClauseOf(2, 0, 1) != clauseTrap {
		t.Fatal("alternating pair was not a trap")
	}
	for j := 0; j <= 3; j++ {
		if IsFirstHit(ps, ts, 2, 0, 1, j) {
			t.Fatalf("trap reported a hit at time %d", j)
		}
	}
	// Negative divisor, same trap: -3 divides neither 1 nor -1.
	if ClauseOf(-3, 0, 1) != clauseTrap {
		t.Fatal("negative divisor divided a non-multiple")
	}
	if IsFirstHit(ps, ts, -3, 0, 1, 0) || IsFirstHit(ps, ts, -3, 0, 1, 1) {
		t.Fatal("negative trap was reported as a hit")
	}
}

// TestSweepCounts demands every clause, no disagreement, and the grid size.
func TestSweepCounts(t *testing.T) {
	seeds := DomainSeeds()
	if seeds != 936 {
		t.Fatalf("seed count %d", seeds)
	}
	cen := RunSweep()
	wantChecks := seeds * uint64(checksPerSeed)
	if cen.Checks != wantChecks {
		t.Fatalf("checks %d want %d", cen.Checks, wantChecks)
	}
	if cen.Failures != 0 {
		t.Fatalf("failures %d", cen.Failures)
	}
	if cen.HitZero == 0 || cen.HitOne == 0 || cen.Trap == 0 {
		t.Fatalf("a clause was empty: %d %d %d", cen.HitZero, cen.HitOne, cen.Trap)
	}
	if cen.HitZero+cen.HitOne+cen.Trap != seeds {
		t.Fatalf("clause total %d seeds %d",
			cen.HitZero+cen.HitOne+cen.Trap, seeds)
	}
	if cen.HitZero == seeds || cen.HitOne == seeds || cen.Trap == seeds {
		t.Fatal("clause predicate is constant")
	}
}

// TestCheckSeedAllocatesNothing checks that a warm seed comparison does not allocate.
func TestCheckSeedAllocatesNothing(t *testing.T) {
	cache := NewCache()
	ps := cache.Pow[:len(cache.Pow)]
	ts := cache.Trap[:len(cache.Trap)]
	var cen Census
	allocs := testing.AllocsPerRun(100, func() {
		cen = Census{}
		checkSeed(ps, ts, 3, -2, 5, &cen)
	})
	if allocs != 0 {
		t.Fatalf("allocations %f", allocs)
	}
}
