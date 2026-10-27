// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedCore checks finite instances of the signed core bound. For
// natural numbers A < m and B >= 0, with N = floor(B / (m - A)), the
// remainder of B is strictly below one more copy of the gap, A*n+B is strictly
// below m*n whenever n >= N+1, and A*n+B stays strictly below m*(N+1) whenever
// n <= N. The floor quotient (A*|n|+B)/m is an integer map obeying the same
// bound on the sampled seeds. Contraction of that quotient is checked only
// when N <= 11; larger radii meet only the shell test on |n| <= 12. The grid
// is a finite certificate, not a proof, and it does not identify the quotient
// with a first-division return of a raw map.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Grid of the certificate. A runs through 0..coreMaxA, the gap m-A runs
// through 1..coreMaxGap, B runs through 0..coreMaxB, the natural comparison
// uses n through 0..coreMaxN, and the quotient map uses seeds through
// -coreMapMax..coreMapMax. The largest product evaluated is m*n = 640.
// The largest value of A*n+B is 344. Both fit in an int64.
const (
	coreMaxA    = 8
	coreMaxGap  = 8
	coreMaxB    = 24
	coreMaxN    = 40
	coreMapMax  = 12
	coreWorkers = 4
)

// Totals counts checks and failures of one slice. Values and Bools, when
// non-nil, receive each compared pair and its truth value. The sweep leaves
// both nil.
type Totals struct {
	Checks   uint64
	Failures uint64
	Values   *[][2]int64
	Bools    *[]bool
}

// Check records one comparison.
func (t *Totals) Check(ok bool) {
	t.Checks++
	if !ok {
		t.Failures++
	}
}

// Observe records one comparison and, when requested, its integers and truth
// value.
func (t *Totals) Observe(left, right int64, ok bool) {
	t.Check(ok)
	if t.Values != nil {
		*t.Values = append(*t.Values, [2]int64{left, right})
	}
	if t.Bools != nil {
		*t.Bools = append(*t.Bools, ok)
	}
}

// CoreRadiusInt returns floor(B / (m - A)) for A < m.
func CoreRadiusInt(A, B, m int64) int64 {
	return B / (m - A)
}

// AbsInt returns the absolute value of a nonnegative or negative seed on the
// documented grid.
func AbsInt(n int64) int64 {
	if n < 0 {
		return -n
	}
	return n
}

// CheckTriple checks the room, descent, invariance and quotient-map statements
// for one admissible triple. The comparison m*hmag <= A*|n|+B is the division
// identity for the nonnegative floor quotient, not a separate estimate.
// Strict quotient contraction is reached only when N <= coreMapMax-1.
func CheckTriple(A, B, m int64, t *Totals) {
	N := CoreRadiusInt(A, B, m)
	gap := m - A
	t.Observe(B, gap*(N+1), B < gap*(N+1))
	for n := int64(0); n <= coreMaxN; n++ {
		if n >= N+1 {
			left, right := A*n+B, m*n
			t.Observe(left, right, left < right)
		} else {
			left, right := A*n+B, m*(N+1)
			t.Observe(left, right, left < right)
		}
	}
	for n := int64(-coreMapMax); n <= coreMapMax; n++ {
		mag := AbsInt(n)
		sum := A*mag + B
		hmag := sum / m
		t.Observe(m*hmag, sum, m*hmag <= sum)
		if mag >= N+1 {
			t.Observe(hmag, mag, hmag < mag)
		} else {
			t.Observe(hmag, N, hmag <= N)
		}
	}
}

// SweepRange checks every triple whose first coefficient lies in [lo, hi].
func SweepRange(lo, hi int64, t *Totals) {
	for A := lo; A <= hi; A++ {
		for gap := int64(1); gap <= coreMaxGap; gap++ {
			m := A + gap
			for B := int64(0); B <= coreMaxB; B++ {
				CheckTriple(A, B, m, t)
			}
		}
	}
}

// SweepCore splits the coefficient range across the workers and sums the
// chunk totals in index order.
func SweepCore() Totals {
	count := coreMaxA + 1
	width := (count + coreWorkers - 1) / coreWorkers
	chunks := make([]Totals, coreWorkers)
	var wg sync.WaitGroup
	for i := 0; i < coreWorkers; i++ {
		lo := int64(i * width)
		hi := lo + int64(width) - 1
		if lo > coreMaxA {
			continue
		}
		if hi > coreMaxA {
			hi = coreMaxA
		}
		wg.Add(1)
		go func(idx int, lo, hi int64) {
			defer wg.Done()
			SweepRange(lo, hi, &chunks[idx])
		}(i, lo, hi)
	}
	wg.Wait()
	var total Totals
	for _, chunk := range chunks {
		total.Checks += chunk.Checks
		total.Failures += chunk.Failures
	}
	return total
}

// SweepControls checks the documented boundary triples outside the loop count.
func SweepControls(t *Totals) {
	N := CoreRadiusInt(2, 7, 3)
	t.Check(N == 7)
	t.Check(2*8+7 < 3*8)
	t.Check(2*7+7 < 3*(N+1))
	t.Check((2*8+7)/3 == 7)
	t.Check((2*7+7)/3 <= N)
	t.Check((2*AbsInt(-8)+7)/3 == 7)
	t.Check(5 < 1*(CoreRadiusInt(0, 5, 1)+1))
	t.Check(3*6+5 < 4*6)
}

// main runs the grid and the controls and exits nonzero on a failure.
func main() {
	grid := SweepCore()
	fmt.Printf("%-14s checks %8d failures %d\n", "core bound",
		grid.Checks, grid.Failures)
	controls := Totals{}
	SweepControls(&controls)
	fmt.Printf("%-14s checks %8d failures %d\n", "controls",
		controls.Checks, controls.Failures)
	total := grid.Checks + controls.Checks
	failures := grid.Failures + controls.Failures
	fmt.Printf("signed core checks: %d, failures: %d\n", total, failures)
	if failures != 0 {
		os.Exit(1)
	}
}
