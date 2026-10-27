// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnClock checks the first-hit clock on one finite grid.
// For each modulus m from 2 through 15 and every residue triple q, c, n in
// {0, ..., m-1}, every time j at which m first divides the affine state
// satisfies j < m. Exact int64 arithmetic is used. The grid does not prove
// the bound for every integer parameter.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Modulus bounds and the worker count. For 2 <= m <= 15, residues
// 0 <= q, c, n < m, and times j <= m, a nonnegative affine state is at most
// (m-1)^(m+1) + (m-1)*((m-1)^m-1)/(m-2) when m > 2.
// At m = 15 that is 14^16 + 14*(14^15-1)/13 < 3*10^18,
// strictly less than 2^63-1. Each product q*A is smaller than the next
// state when c >= 0, so no int64 product overflows on this grid.
const (
	modulusMin   = 2
	modulusMax   = 15
	clockWorkers = 4
)

// Totals counts comparisons, disagreements, and first hits of one sweep.
type Totals struct {
	Checks   uint64
	Failures uint64
	Hits     uint64
}

// Check records one comparison.
func (t *Totals) Check(ok bool) {
	t.Checks++
	if !ok {
		t.Failures++
	}
}

// Add accumulates a worker total into the receiver.
func (t *Totals) Add(other Totals) {
	t.Checks += other.Checks
	t.Failures += other.Failures
	t.Hits += other.Hits
}

// ModulusAbs returns |D|. The argument is a stated modulus, never zero,
// and never the most negative int64.
func ModulusAbs(D int64) int64 {
	if D < 0 {
		return -D
	}
	return D
}

// AffineStep applies one affine branch q*cur+c.
func AffineStep(q, c, cur int64) int64 {
	return q*cur + c
}

// AffineAt returns A_j(q,c,n) by iterating the affine branch from n.
func AffineAt(q, c, n int64, j int) int64 {
	cur := n
	for i := 0; i < j; i++ {
		cur = AffineStep(q, c, cur)
	}
	return cur
}

// IsFirstHit reports that D divides A_j(q,c,n) and divides no earlier
// affine state. D is nonzero. The result is false when j is not that time.
func IsFirstHit(q, c, D, n int64, j int) bool {
	cur := n
	for i := 0; i < j; i++ {
		if cur%D == 0 {
			return false
		}
		cur = AffineStep(q, c, cur)
	}
	return cur%D == 0
}

// FirstHitBelowModulus reports that j is a first hit and j < |D|.
// It is false when j is not a first hit, including when j >= |D|.
func FirstHitBelowModulus(q, c, D, n int64, j int) bool {
	if !IsFirstHit(q, c, D, n, j) {
		return false
	}
	return j < int(ModulusAbs(D))
}

// SweepModulus checks every residue triple at modulus m. Times run through
// 0, ..., m, so a first hit at time m is a clock failure. Each triple
// contributes at most one hit.
func SweepModulus(m int64) Totals {
	var t Totals
	limit := int(m)
	for q := int64(0); q < m; q++ {
		for c := int64(0); c < m; c++ {
			for n := int64(0); n < m; n++ {
				for j := 0; j <= limit; j++ {
					hit := IsFirstHit(q, c, m, n, j)
					below := FirstHitBelowModulus(q, c, m, n, j)
					t.Check(below == (hit && j < limit))
					if hit {
						t.Check(j < limit)
						t.Hits++
					}
				}
			}
		}
	}
	return t
}

// SweepClock splits the moduli 2, ..., 15 across workers and sums totals.
func SweepClock() Totals {
	count := modulusMax - modulusMin + 1
	parts := make([]Totals, count)
	var wg sync.WaitGroup
	for worker := 0; worker < clockWorkers; worker++ {
		wg.Add(1)
		go func(worker int) {
			defer wg.Done()
			for i := worker; i < count; i += clockWorkers {
				parts[i] = SweepModulus(int64(modulusMin + i))
			}
		}(worker)
	}
	wg.Wait()
	var total Totals
	for _, part := range parts {
		total.Add(part)
	}
	return total
}

// main prints the number of comparisons and the number of first hits.
// It exits nonzero when a first hit is not strictly below its modulus.
func main() {
	total := SweepClock()
	fmt.Printf("clock checks: %d, hits: %d, failures: %d\n",
		total.Checks, total.Hits, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
