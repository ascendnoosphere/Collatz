// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere
package main

import (
	"math"
	"math/big"
	"testing"
)

// TestPeriods checks least positive returns, critical cases, and forbidden nonunit maps.
func TestPeriods(t *testing.T) {
	cases := []struct {
		p Parameters
		m uint64
	}{
		{Parameters{2, 1, 3}, 2},
		{Parameters{3, 1, 2}, 2},
		{Parameters{2, 0, 3}, 1},
		{Parameters{2, 1, 5}, 4},
		{Parameters{4, 1, 5}, 2},
		{Parameters{4, 1, 3}, 3},
		{Parameters{2, 3, 3}, 1},
		{Parameters{math.MaxUint64, math.MaxUint64, 2}, 2},
	}
	for _, item := range cases {
		m, err := AccessPeriod(item.p)
		if err != nil || m != item.m {
			t.Fatalf("period %+v: got %d, %v; want %d", item.p, m, err, item.m)
		}
	}
	for _, p := range []Parameters{{1, 1, 3}, {2, 1, 4}, {2, 1, 1}, {2, 1, MaxModulus + 1}} {
		if _, err := AccessPeriod(p); err == nil {
			t.Fatalf("accepted invalid parameters: %+v", p)
		}
	}
}

// TestRawClocks distinguishes an initial division, consecutive divisions, and affine entry.
func TestRawClocks(t *testing.T) {
	p := Parameters{2, 1, 3}
	var w Workspace
	w.Initialize()
	cases := []struct {
		n, h, ticks, endpoint, multiplier uint64
	}{
		{1, 7, 14, 1, 128}, {3, 1, 1, 1, 1}, {9, 2, 2, 1, 1},
		{4, 2, 3, 1, 2}, {7, 0, 0, 7, 1},
	}
	for _, item := range cases {
		w.Seed.SetUint64(item.n)
		ok, err := w.Run(p, 2, item.h, &w.Seed)
		if err != nil || !ok || w.Ticks != item.ticks || w.State.Uint64() != item.endpoint ||
			w.Multiplier.Uint64() != item.multiplier {
			t.Fatalf("incorrect legal block prefix: %+v, %v", item, err)
		}
		count, err := w.RawClock(p, &w.Seed, w.Ticks)
		if err != nil || count != item.h || w.RawState.Cmp(&w.State) != 0 {
			t.Fatalf("raw clock failed: %+v, %v", item, err)
		}
	}
	w.Seed.SetUint64(2)
	ok, err := w.Run(p, 2, 1, &w.Seed)
	if err != nil || ok || w.Divisions != 0 {
		t.Fatalf("residue 2 should fail the complete first-division search")
	}
	count, err := w.RawClock(p, &w.Seed, 128)
	if err != nil || count != 0 {
		t.Fatalf("unexpected division on the affine-only control: %d, %v", count, err)
	}
	w.Seed.SetUint64(7)
	ok, err = w.Run(p, 2, 2, &w.Seed)
	if err != nil || ok || w.Divisions != 1 {
		t.Fatal("seed 7 reaches the trap 5 after one division, not a legal depth-two class")
	}
	// Aliasing a retained parameter must not change the seed before its snapshot.
	w.Q.SetUint64(4)
	ok, err = w.Run(p, 2, 2, &w.Q)
	if err != nil || !ok || w.State.Uint64() != 1 {
		t.Fatal("aliased block seed was overwritten by the multiplier parameter")
	}
	w.Q.SetUint64(4)
	count, err = w.RawClock(p, &w.Q, 3)
	if err != nil || count != 2 || w.RawState.Uint64() != 1 {
		t.Fatal("aliased raw-clock seed was overwritten before execution")
	}
}

// TestLargeExactShift checks a lifted cycle cylinder far beyond machine integer precision.
func TestLargeExactShift(t *testing.T) {
	var w Workspace
	w.Initialize()
	var shift, power, seed, expected big.Int
	shift.Lsh(big.NewInt(1), 256)
	power.Exp(big.NewInt(3), big.NewInt(7), nil)
	seed.Mul(&shift, &power)
	seed.Add(&seed, big.NewInt(1))
	ok, err := w.Run(Parameters{2, 1, 3}, 2, 7, &seed)
	expected.Lsh(&shift, 7)
	expected.Add(&expected, big.NewInt(1))
	if err != nil || !ok || w.State.Cmp(&expected) != 0 || w.Multiplier.Uint64() != 128 {
		t.Fatalf("exact shifted endpoint failed: %v", err)
	}
	count, err := w.RawClock(Parameters{2, 1, 3}, &seed, w.Ticks)
	if err != nil || count != 7 || w.RawState.Cmp(&expected) != 0 {
		t.Fatalf("large raw-clock recovery failed: %v", err)
	}
}

// TestCensuses checks strict, critical, and zero-offset lift families exhaustively.
func TestCensuses(t *testing.T) {
	var w, v Workspace
	w.Initialize()
	v.Initialize()
	cases := []struct {
		p        Parameters
		h, count uint64
	}{
		{Parameters{2, 1, 3}, 2, 4},
		{Parameters{3, 1, 2}, 3, 8},
		{Parameters{2, 0, 3}, 3, 1},
		{Parameters{2, 1, 5}, 3, 64},
	}
	for _, item := range cases {
		row, err := Census(item.p, item.h, &w, &v)
		if err != nil || row.Classes != item.count || row.LiftsChecked != item.count*item.p.D {
			t.Fatalf("census %+v: %+v, %v", item, row, err)
		}
		if row.RawClocksChecked != row.Modulus+item.count*item.p.D {
			t.Fatalf("raw checks omitted accepted or rejected sources: %+v", row)
		}
	}
}

// TestIntervals checks the explicit boundary term on complete and partial source blocks.
func TestIntervals(t *testing.T) {
	p := Parameters{2, 1, 5}
	var w Workspace
	w.Initialize()
	count, positive := uint64(0), uint64(0)
	for X := uint64(0); X <= 257; X++ {
		if count > 64*((X+124)/125) {
			t.Fatalf("exact ceiling interval bound failed at X=%d", X)
		}
		w.Seed.SetUint64(X)
		ok, err := w.Run(p, 4, 3, &w.Seed)
		if err != nil {
			t.Fatal(err)
		}
		if ok {
			count++
			if X > 0 {
				positive++
			}
		}
		// The closed positive interval keeps its residue-zero right endpoint.
		if positive > 64*((X+124)/125) || positive > X {
			t.Fatalf("positive interval bound failed at X=%d", X)
		}
	}
}

// TestRejectedBudgets prevents wrapped powers, negative seeds, and fabricated periods.
func TestRejectedBudgets(t *testing.T) {
	if _, err := Power(2, 64, math.MaxUint64); err == nil {
		t.Fatal("accepted a wrapped source modulus")
	}
	var w Workspace
	w.Initialize()
	p := Parameters{2, 1, 3}
	for _, item := range []struct {
		m, h uint64
		seed *big.Int
	}{
		{1, 2, big.NewInt(1)}, {0, 2, big.NewInt(1)},
		{2, 2, nil}, {2, 2, big.NewInt(-1)}, {2, MaxBits + 1, big.NewInt(1)},
		{2, 2000, big.NewInt(1)},
	} {
		if _, err := w.Run(p, item.m, item.h, item.seed); err == nil {
			t.Fatalf("accepted invalid block budget: %+v", item)
		}
	}
	if _, err := w.RawClock(Parameters{2, 1, 0}, big.NewInt(1), 1); err == nil {
		t.Fatal("accepted a zero divisor in the independent raw clock")
	}
	if _, err := Power(2, 0, 0); err == nil {
		t.Fatal("accepted a zeroth power outside the enumeration budget")
	}
	for _, item := range []struct{ base, exponent, limit, want uint64 }{
		{0, math.MaxUint64, 0, 0}, {1, math.MaxUint64, 1, 1}, {2, 0, 1, 1},
	} {
		got, err := Power(item.base, item.exponent, item.limit)
		if err != nil || got != item.want {
			t.Fatalf("constant or zeroth power budget failed: %+v, %v", item, err)
		}
	}
	var v Workspace
	v.Initialize()
	if _, err := Census(Parameters{3, 1, 2}, 20, &w, &v); err == nil {
		t.Fatal("accepted a next source-digit level larger than MaxSeeds")
	}
}

// TestNoHotAllocations verifies the preallocated large-integer prefix and raw loops.
func TestNoHotAllocations(t *testing.T) {
	var w Workspace
	w.Initialize()
	var shift, power, seed big.Int
	shift.Lsh(big.NewInt(1), 256)
	power.Exp(big.NewInt(3), big.NewInt(7), nil)
	seed.Mul(&shift, &power)
	seed.Add(&seed, big.NewInt(1))
	p := Parameters{2, 1, 3}
	allocations := testing.AllocsPerRun(100, func() {
		ok, err := w.Run(p, 2, 7, &seed)
		if err != nil || !ok {
			panic("invalid allocation fixture")
		}
		if count, err := w.RawClock(p, &seed, w.Ticks); err != nil || count != 7 {
			panic("invalid raw-clock allocation fixture")
		}
	})
	if allocations != 0 {
		t.Fatalf("hot loops allocated %g times per run", allocations)
	}
}

// TestParallelRepeatability checks disjoint chunk assembly and stable publication order.
func TestParallelRepeatability(t *testing.T) {
	models := []Parameters{{2, 1, 3}, {3, 1, 2}, {2, 0, 3}, {2, 1, 5}}
	a, err := Execute(models, 3)
	if err != nil {
		t.Fatal(err)
	}
	b, err := Execute(models, 3)
	if err != nil {
		t.Fatal(err)
	}
	if len(a) != 12 || len(a) != len(b) {
		t.Fatal("missing deterministic records")
	}
	for i := range a {
		if a[i] != b[i] {
			t.Fatalf("chunk-order mismatch at %d", i)
		}
	}
}
