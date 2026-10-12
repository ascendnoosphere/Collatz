// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestAffineRejectsUnitSlack fails if AffineIs is replaced by true.
func TestAffineRejectsUnitSlack(t *testing.T) {
	w := NewWorkspace()
	// j = 5, c = 4, n = -7 gives the state -7+20 = 13.
	w.Prepare(1, 5)
	if w.Pow != 1 || w.Trap != 5 {
		t.Fatalf("prepared power %d sum %d", w.Pow, w.Trap)
	}
	if !AffineIs(w, 4, -7, 5, 13) {
		t.Fatal("unit translation was rejected")
	}
	if AffineIs(w, 4, -7, 5, 14) {
		t.Fatal("unit slack was accepted")
	}
}

// TestReturnRejectsUnitSlack fails if ReturnIs or IsFirstHit is replaced by true.
func TestReturnRejectsUnitSlack(t *testing.T) {
	cache := NewCache()
	cache.Load(1)
	// d = 2 does not divide the seed 1, so time zero is not a hit.
	if IsFirstHit(cache, 0, 2, 1, 0) {
		t.Fatal("a non-multiple was reported as a hit")
	}
	if ReturnIs(cache, 0, 2, 1, 0, 0) || ReturnIs(cache, 0, 2, 1, 0, 1) {
		t.Fatal("a non-hit was reported as a return")
	}
	// d = -2 divides 2, and the quotient is -1.
	if !IsFirstHit(cache, 0, -2, 2, 0) {
		t.Fatal("a negative divisor rejected a multiple")
	}
	if !ReturnIs(cache, 0, -2, 2, 0, -1) {
		t.Fatal("negative division was rejected")
	}
	if ReturnIs(cache, 0, -2, 2, 0, 0) {
		t.Fatal("unit slack was accepted")
	}
	// c = 1, d = 2, n = 1 hits at time 1: the state is 2 and the quotient is 1.
	if IsFirstHit(cache, 1, 2, 1, 0) {
		t.Fatal("an earlier non-multiple was accepted")
	}
	if !ReturnIs(cache, 1, 2, 1, 1, 1) {
		t.Fatal("translation return was rejected")
	}
	if ReturnIs(cache, 1, 2, 1, 1, 2) {
		t.Fatal("unit slack was accepted on a later hit")
	}
	if ReturnIs(cache, 1, 2, 1, 2, 1) {
		t.Fatal("a time after the first hit was accepted")
	}
	// c = 1, d = 3, n = -4 hits at time 1 with quotient -1.
	if !ReturnIs(cache, 1, 3, -4, 1, -1) {
		t.Fatal("negative numerator was rejected")
	}
	if ReturnIs(cache, 1, 3, -4, 1, 0) {
		t.Fatal("unit slack was accepted for a negative quotient")
	}
}

// TestMagnitudeRejectsSlack fails if MagnitudeIs or CoreAtSeed is replaced by true.
func TestMagnitudeRejectsSlack(t *testing.T) {
	cache := NewCache()
	cache.Load(1)
	// |−2| * |−1| = 2 and |2| + 0*|0| = 2, so the bound is tight.
	if !MagnitudeIs(cache, 0, -2, 2, 0, 2) {
		t.Fatal("tight magnitude bound was rejected")
	}
	if MagnitudeIs(cache, 0, -2, 2, 0, 1) {
		t.Fatal("a short magnitude bound was accepted")
	}
	if !CoreAtSeed(cache, 1, 0, -2, 2, 0, 0) {
		t.Fatal("tight core bound was rejected")
	}
	if CoreAtSeed(cache, 1, 0, -2, 2, 0, -1) {
		t.Fatal("a short core offset was accepted")
	}
	// |3| * |−1| = 3 and |−4| + 1*|1| = 5.
	if !MagnitudeIs(cache, 1, 3, -4, 1, 5) {
		t.Fatal("negative magnitude bound was rejected")
	}
	if MagnitudeIs(cache, 1, 3, -4, 1, 2) {
		t.Fatal("a short negative magnitude bound was accepted")
	}
	if MagnitudeIs(cache, 0, 2, 1, 0, 0) {
		t.Fatal("a non-hit satisfied the magnitude predicate")
	}
	if CoreAtSeed(cache, 1, 0, 2, 1, 0, 0) {
		t.Fatal("a non-hit satisfied the core predicate")
	}
	// A mismatched multiplier is not the loaded unit cache.
	if CoreAtSeed(cache, 2, 0, -2, 2, 0, 0) {
		t.Fatal("a multiplier other than 1 was accepted")
	}
}

// TestDomainAndSweep pins the grid size and demands zero disagreements.
func TestDomainAndSweep(t *testing.T) {
	cCount := uint64(unitCMax - unitCMin + 1)
	nCount := uint64(unitNMax - unitNMin + 1)
	jCount := uint64(unitJMax + 1)
	product := cCount*nCount*jCount + cCount*nCount*jCount*6
	if product != 33579 {
		t.Fatalf("domain product %d", product)
	}
	if DomainSize() != product {
		t.Fatalf("domain %d product %d", DomainSize(), product)
	}
	got := RunUnitSweep()
	if got.Checks != product || got.Failures != 0 {
		t.Fatalf("checks %d failures %d", got.Checks, got.Failures)
	}
	slots := cCount * nCount * jCount * 6
	if got.Hits == 0 || got.Hits == slots {
		t.Fatalf("first-hit predicate is constant: hits %d slots %d", got.Hits, slots)
	}
}

// TestPrepareAllocatesNothing checks that a warm unit update does not allocate.
func TestPrepareAllocatesNothing(t *testing.T) {
	w := NewWorkspace()
	cache := NewCache()
	cache.Load(1)
	w.Prepare(1, unitJMax)
	allocs := testing.AllocsPerRun(100, func() {
		w.Prepare(1, unitJMax)
		if !AffineIs(w, -6, -20, unitJMax, -20+int64(unitJMax)*(-6)) {
			panic("affine form failed inside the allocation probe")
		}
		if !ReturnIs(cache, 0, -2, 2, 0, -1) {
			panic("return failed inside the allocation probe")
		}
	})
	if allocs != 0 {
		t.Fatalf("prepare allocated %v times per run", allocs)
	}
}
