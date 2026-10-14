// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math"
	"testing"
)

// TestCensus checks every supported parameter tuple, including all gcd branches.
func TestCensus(t *testing.T) {
	for q := uint64(2); q <= MaxQ; q++ {
		row := ScanQ(q)
		if row.Err != nil {
			t.Fatal(row.Err)
		}
		want := int(MaxK * MaxT * (MaxSeed - MaxSeed/q))
		if row.Seeds != want || row.Seeds != row.Escape+row.Return || row.Return == 0 {
			t.Fatalf("q=%d census=%+v want=%d", q, row, want)
		}
	}
}

// TestReturns distinguishes strict descent, fixed small returns, and class changes.
func TestReturns(t *testing.T) {
	rows := []struct {
		w                              Witness
		delay, clip, value, floor, end uint64
	}{
		{Witness{2, 2, 1, 1}, 1, 2, 1, 5, 4},
		{Witness{3, 2, 1, 8}, 1, 1, 5, 5, 5},
		{Witness{4, 2, 6, 2}, 1, 2, 2, 18, 4},
		{Witness{4, 2, 2, 2}, 1, 1, 5, 6, 5},
	}
	ws := Workspace{}
	for _, row := range rows {
		got, err := EvalReturn(row.w, &ws)
		if err != nil || got.Delay != row.delay || got.Clip != row.clip ||
			got.J != row.value || got.Floor != row.floor || got.Clock != row.end {
			t.Fatalf("w=%+v return=%+v err=%v", row.w, got, err)
		}
	}
	if _, err := CheckEscape(Witness{4, 2, 2, 5}, &ws); err != nil {
		t.Fatal("the small return did not enter the escape class:", err)
	}
}

// TestFirstDivision independently checks the clipped division time at each returned anchor.
func TestFirstDivision(t *testing.T) {
	ws := Workspace{}
	for q := uint64(2); q <= 6; q++ {
		for k := uint64(1); k <= 3; k++ {
			for offset := uint64(1); offset <= 4; offset++ {
				cache, err := NewCache(q, k, offset)
				if err != nil {
					t.Fatal(err)
				}
				for n := uint64(1); n <= 96; n++ {
					if n%q == 0 || n%cache.g != 0 {
						continue
					}
					ev, err := EvalReturn(Witness{q, k, offset, n}, &ws)
					if err != nil {
						t.Fatal(err)
					}
					state := ev.State
					for i := uint64(0); ; i++ {
						if state%cache.d == 0 {
							if i != k-ev.Clip || state/cache.d != ev.J {
								t.Fatalf("first division q=%d k=%d n=%d i=%d", q, k, n, i)
							}
							break
						}
						if i >= k {
							t.Fatal("no division by the proved clock")
						}
						state, err = RawStep(q, cache.c, cache.d, state)
						if err != nil {
							t.Fatal(err)
						}
					}
				}
			}
		}
	}
}

// TestArithmetic checks constant bases, the largest geometric sum, and overflow boundaries.
func TestArithmetic(t *testing.T) {
	for _, base := range []uint64{0, 1} {
		value, err := Pow(base, math.MaxUint64)
		if err != nil || value != base {
			t.Fatalf("constant power base=%d value=%d err=%v", base, value, err)
		}
	}
	if value, err := Geom(2, 64); err != nil || value != math.MaxUint64 {
		t.Fatalf("largest geometric sum value=%d err=%v", value, err)
	}
	if value, err := Geom(1, math.MaxUint64); err != nil || value != math.MaxUint64 {
		t.Fatal("constant-base geometric sum")
	}
	if value, err := Geom(0, math.MaxUint64); err != nil || value != 1 {
		t.Fatal("zero-base geometric sum")
	}
	if _, err := Pow(2, 64); err == nil {
		t.Fatal("overflowing power accepted")
	}
	if _, err := Geom(2, 65); err == nil {
		t.Fatal("overflowing geometric sum accepted")
	}
	if _, err := Mul(math.MaxUint64, 2); err == nil {
		t.Fatal("overflowing product accepted")
	}
	if _, err := Add(math.MaxUint64, 1); err == nil {
		t.Fatal("overflowing sum accepted")
	}
	if _, err := Sub(0, 1); err == nil {
		t.Fatal("negative difference accepted")
	}
	if j, err := Clip(2, 63, 0); err != nil || j != 63 {
		t.Fatal("zero-state clip")
	}
	if _, err := Clip(2, math.MaxUint64, 1); err == nil {
		t.Fatal("unbounded clip accepted")
	}
}

// TestInvalidInputs requires rejection before an unsupported loop or division.
func TestInvalidInputs(t *testing.T) {
	ws := Workspace{}
	rows := []Witness{{1, 1, 1, 1}, {9, 1, 1, 1}, {2, 0, 1, 1},
		{2, math.MaxUint64, 1, 1}, {2, 1, 0, 1}, {2, 1, 9, 1},
		{2, 1, 1, 0}, {2, 1, 1, 257}, {2, 1, 1, 2}}
	for _, w := range rows {
		if _, err := CheckEscape(w, &ws); err == nil {
			t.Fatalf("escape accepted invalid witness %+v", w)
		}
		if _, err := EvalReturn(w, &ws); err == nil {
			t.Fatalf("return accepted invalid witness %+v", w)
		}
	}
	if _, err := EvalReturn(Witness{2, 2, 2, 1}, &ws); err == nil {
		t.Fatal("return accepted the escape branch")
	}
	if _, err := CheckEscape(Witness{2, 2, 1, 1}, &ws); err == nil {
		t.Fatal("escape accepted the return branch")
	}
	if _, err := CheckReturn(Witness{2, 2, 1, 1}, nil); err == nil {
		t.Fatal("nil workspace accepted")
	}
	if _, err := ws.Iterate(2, 2, 2, math.MaxUint64, 1); err == nil {
		t.Fatal("unbounded tick budget accepted")
	}
	if _, err := ws.Iterate(2, 2, 0, 0, 1); err == nil {
		t.Fatal("invalid divisor accepted on zero ticks")
	}
	if _, err := RawStep(3, 1, 2, math.MaxUint64); err == nil {
		t.Fatal("overflowing raw step accepted")
	}
	if ScanQ(1).Err == nil || ScanQ(9).Err == nil {
		t.Fatal("unsupported census q accepted")
	}
}

// TestAllocations keeps both successful mathematical branches allocation-free.
func TestAllocations(t *testing.T) {
	ws := Workspace{}
	allocs := testing.AllocsPerRun(100, func() {
		if _, err := CheckReturn(Witness{4, 2, 2, 2}, &ws); err != nil {
			t.Fatal(err)
		}
		if _, err := CheckEscape(Witness{4, 2, 2, 5}, &ws); err != nil {
			t.Fatal(err)
		}
	})
	if allocs != 0 {
		t.Fatalf("successful branch allocations=%g", allocs)
	}
}
