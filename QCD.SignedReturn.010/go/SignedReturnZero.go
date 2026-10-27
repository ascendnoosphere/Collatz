// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnZero checks the zero-multiplier return on one finite
// grid. The multiplier is 0, so the affine state is the seed at time 0 and the
// offset at every positive time. If d divides n, the return is n/d at time 0.
// If d misses n but divides c, the return is the constant c/d at time 1. If d
// misses both, there is no return. Exact int64 arithmetic is used. With
// |c| <= 12, |n| <= 24 and |d| in {2,3,4,5}, every state and every exact
// quotient fits in an int64. Agreement on this grid does not prove the
// trichotomy for every integer.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the finite check. The eight divisors are ±2, ±3, ±4, ±5.
// Offsets run through [-zeroCAbs, zeroCAbs] and seeds through
// [-zeroNAbs, zeroNAbs]. Times 0 through zeroJMax test that a hit at 0 or 1
// is not reported again later. The multiplier is identically zero, so no
// power is stored.
const (
	zeroCAbs    = 12
	zeroNAbs    = 24
	zeroJMax    = 8
	zeroWorkers = 4
	zeroDivs    = 8
)

// zeroDivisors is the signed divisor list used by every sweep.
var zeroDivisors = [zeroDivs]int64{-5, -4, -3, -2, 2, 3, 4, 5}

// Totals counts comparisons and disagreements of one sweep.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// Add accumulates a worker total into the receiver.
func (t *Totals) Add(other Totals) {
	t.Checks += other.Checks
	t.Failures += other.Failures
}

// Divides reports whether d divides a. Every divisor on the grid is nonzero.
func Divides(d, a int64) bool {
	return a%d == 0
}

// ZeroAffineState is the seed at time 0 and the offset at every later time.
func ZeroAffineState(c, n int64, j int) int64 {
	if j == 0 {
		return n
	}
	return c
}

// IsFirstHit reports whether j is the first time d divides the zero-multiplier
// affine state. A nonpositive index is not a time.
func IsFirstHit(d, c, n int64, j int) bool {
	if j < 0 || !Divides(d, ZeroAffineState(c, n, j)) {
		return false
	}
	for i := 0; i < j; i++ {
		if Divides(d, ZeroAffineState(c, n, i)) {
			return false
		}
	}
	return true
}

// ZeroReturn reports the first-hit time and the quotient of that state by d.
// The boolean is false when no time is a hit. A double miss returns no value:
// the constant offset is not treated as a return.
func ZeroReturn(d, c, n int64) (j int, quot int64, ok bool) {
	if Divides(d, n) {
		return 0, n / d, true
	}
	if Divides(d, c) {
		return 1, c / d, true
	}
	return 0, 0, false
}

// PositiveSeedReturns reports whether a positive seed has a positive-time
// return equal to itself when the offset is zero. The only positive-time
// quotient in that case is zero, so the result is false for every positive n.
func PositiveSeedReturns(d, n int64) bool {
	if n <= 0 {
		return false
	}
	j, quot, ok := ZeroReturn(d, 0, n)
	return ok && j >= 1 && quot == n
}

// RawStep applies one raw step at multiplier zero. Division is exact when d
// Divides n, and Go truncates toward zero.
func RawStep(c, d, n int64) int64 {
	if Divides(d, n) {
		return n / d
	}
	return c
}

// ExpectedHit is the case split: time 0 if d divides n, time 1 if d misses n
// but divides c, and no time otherwise.
func ExpectedHit(d, c, n int64, j int) bool {
	if j == 0 {
		return Divides(d, n)
	}
	if j == 1 {
		return !Divides(d, n) && Divides(d, c)
	}
	return false
}

// ReturnAgrees checks the quotient named by the same case split.
func ReturnAgrees(d, c, n int64) bool {
	j, quot, ok := ZeroReturn(d, c, n)
	if Divides(d, n) {
		return ok && j == 0 && quot == n/d
	}
	if Divides(d, c) {
		return ok && j == 1 && quot == c/d
	}
	return !ok
}

// RawAgrees checks the return against the raw step. A double miss must not
// divide at any time through zeroJMax, and its state must be c after time 0.
func RawAgrees(d, c, n int64) bool {
	if Divides(d, n) {
		return RawStep(c, d, n) == n/d
	}
	if Divides(d, c) {
		first := RawStep(c, d, n)
		if first != c {
			return false
		}
		return RawStep(c, d, first) == c/d
	}
	cur := n
	for j := 0; j <= zeroJMax; j++ {
		if Divides(d, cur) {
			return false
		}
		cur = RawStep(c, d, cur)
		if cur != c {
			return false
		}
	}
	return true
}

// CheckTuple records the state, the hit predicate, the return, and the raw
// step for one divisor, offset, and seed. A positive seed at offset zero
// contributes one extra comparison.
func CheckTuple(d, c, n int64, total *Totals) {
	for j := 0; j <= zeroJMax; j++ {
		want := n
		if j > 0 {
			want = c
		}
		total.Checks++
		if ZeroAffineState(c, n, j) != want {
			total.Failures++
		}
		total.Checks++
		if IsFirstHit(d, c, n, j) != ExpectedHit(d, c, n, j) {
			total.Failures++
		}
	}
	total.Checks++
	if !ReturnAgrees(d, c, n) {
		total.Failures++
	}
	total.Checks++
	if !RawAgrees(d, c, n) {
		total.Failures++
	}
	if c == 0 && n > 0 {
		total.Checks++
		if PositiveSeedReturns(d, n) {
			total.Failures++
		}
	}
}

// SweepBetween checks every divisor and seed on a closed offset interval.
func SweepBetween(lo, hi int64) Totals {
	var total Totals
	divs := zeroDivisors[:]
	divs = divs[:len(divs)]
	for c := lo; c <= hi; c++ {
		for i := 0; i < len(divs); i++ {
			d := divs[i]
			for n := int64(-zeroNAbs); n <= int64(zeroNAbs); n++ {
				CheckTuple(d, c, n, &total)
			}
		}
	}
	return total
}

// DomainChecks is the number of comparisons in one full sweep.
func DomainChecks() uint64 {
	cs := uint64(2*zeroCAbs + 1)
	ns := uint64(2*zeroNAbs + 1)
	js := uint64(zeroJMax + 1)
	base := uint64(zeroDivs) * cs * ns
	// Two comparisons at each time, then the return and the raw step.
	per := base * (2*js + 2)
	pos := uint64(zeroDivs * zeroNAbs)
	return per + pos
}

// RunSweep splits the offset range across workers and sums their totals.
func RunSweep() Totals {
	span := 2*zeroCAbs + 1
	width := (span + zeroWorkers - 1) / zeroWorkers
	parts := make([]Totals, zeroWorkers)
	var wg sync.WaitGroup
	for w := 0; w < zeroWorkers; w++ {
		lo := -zeroCAbs + w*width
		hi := lo + width - 1
		if lo > zeroCAbs {
			continue
		}
		if hi > zeroCAbs {
			hi = zeroCAbs
		}
		wg.Add(1)
		go func(idx, lo, hi int) {
			defer wg.Done()
			parts[idx] = SweepBetween(int64(lo), int64(hi))
		}(w, lo, hi)
	}
	wg.Wait()
	var total Totals
	for i := 0; i < len(parts); i++ {
		total.Add(parts[i])
	}
	return total
}

// main prints the number of comparisons and exits nonzero on a disagreement.
func main() {
	total := RunSweep()
	fmt.Printf("zero return checks: %d, failures: %d\n", total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
