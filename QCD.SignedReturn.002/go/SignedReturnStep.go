// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnStep checks the first-hit step on one finite grid.
// If the affine state meets D at time j and at no earlier time, with j at
// most 8, the raw state at j equals the affine state and the next raw step
// equals that state divided once by D. If no such j exists, no raw or affine
// state at time at most 8 is divisible by D. Exact int64 arithmetic is used.
// The grid does not prove the identities for every integer parameter.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the finite check. Multipliers and offsets run through
// [-stepAbsCoeff, stepAbsCoeff], seeds through [-stepAbsSeed, stepAbsSeed],
// and times through 0..stepMaxJ. The six divisors are stepDivisors. On this
// rectangle every affine state of time at most 8 satisfies
// |q|^j*|n| + |c|*sum_{i<j}|q|^i <= 4^8*8 + 4*(4^8-1)/3 = 611668,
// and a raw state through time 8 is no larger, so no int64 product overflows.
const (
	stepAbsCoeff = 4
	stepAbsSeed  = 8
	stepMaxJ     = 8
	stepWorkers  = 3
)

// stepDivisors is the signed divisor list ±2, ±3, ±5. None is zero.
var stepDivisors = [6]int64{-5, -3, -2, 2, 3, 5}

// Totals counts comparisons and disagreements of one sweep.
type Totals struct {
	Checks   uint64
	Failures uint64
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
}

// PowInt returns q^j for a nonnegative exponent on the stated grid.
func PowInt(q int64, j int) int64 {
	out := int64(1)
	for i := 0; i < j; i++ {
		out *= q
	}
	return out
}

// TrapSum returns U_j(q), the sum of q^0 through q^(j-1), with U_0(q) = 0.
func TrapSum(q int64, j int) int64 {
	sum := int64(0)
	pow := int64(1)
	for i := 0; i < j; i++ {
		sum += pow
		pow *= q
	}
	return sum
}

// AffineState returns q^j*n + c*U_j(q).
func AffineState(q, c int64, j int, n int64) int64 {
	return PowInt(q, j)*n + c*TrapSum(q, j)
}

// Divides reports whether D divides n. D is never zero on the stated grid.
func Divides(D, n int64) bool {
	return n%D == 0
}

// RawStep applies one raw step. Go truncation toward zero agrees with the
// exact quotient when D divides n.
func RawStep(q, c, D, n int64) int64 {
	if Divides(D, n) {
		return n / D
	}
	return q*n + c
}

// RawIterate returns the raw state at time j.
func RawIterate(q, c, D, n int64, j int) int64 {
	cur := n
	for i := 0; i < j; i++ {
		cur = RawStep(q, c, D, cur)
	}
	return cur
}

// IsFirstHit reports that D divides the affine state at j and at no earlier time.
func IsFirstHit(q, c, D, n int64, j int) bool {
	if !Divides(D, AffineState(q, c, j, n)) {
		return false
	}
	for i := 0; i < j; i++ {
		if Divides(D, AffineState(q, c, i, n)) {
			return false
		}
	}
	return true
}

// FirstHitBy returns the least first-hit time at most maxJ, if one exists.
func FirstHitBy(q, c, D, n int64, maxJ int) (int, bool) {
	for j := 0; j <= maxJ; j++ {
		if IsFirstHit(q, c, D, n, j) {
			return j, true
		}
	}
	return 0, false
}

// RawPrefixUndivided reports that D divides no raw state at time i <= maxJ.
func RawPrefixUndivided(q, c, D, n int64, maxJ int) bool {
	cur := n
	for i := 0; i <= maxJ; i++ {
		if Divides(D, cur) {
			return false
		}
		cur = RawStep(q, c, D, cur)
	}
	return true
}

// FirstHitStepHolds is the checked predicate. It is false unless j is a first
// hit, the raw state equals the affine state, and the next raw step equals
// that state divided once by D. Replacing the body by a constant true makes
// the non-hit tests fail.
func FirstHitStepHolds(q, c, D, n int64, j int) bool {
	if !IsFirstHit(q, c, D, n, j) {
		return false
	}
	state := AffineState(q, c, j, n)
	got := RawIterate(q, c, D, n, j)
	if got != state {
		return false
	}
	next := RawStep(q, c, D, got)
	quot := state / D
	return next == quot && quot*D == state
}

// CheckSeed checks both identities when a first hit occurs by time 8, and
// checks that the prefix is undivided when none occurs.
func CheckSeed(q, c, D, n int64) Totals {
	var t Totals
	j, ok := FirstHitBy(q, c, D, n, stepMaxJ)
	if ok {
		state := AffineState(q, c, j, n)
		got := RawIterate(q, c, D, n, j)
		next := RawStep(q, c, D, got)
		quot := state / D
		t.Check(FirstHitStepHolds(q, c, D, n, j))
		t.Check(got == state)
		t.Check(next == quot && quot*D == state)
		for i := 0; i < j; i++ {
			earlier := RawIterate(q, c, D, n, i)
			t.Check(!Divides(D, earlier))
			t.Check(!Divides(D, AffineState(q, c, i, n)))
			t.Check(!FirstHitStepHolds(q, c, D, n, i))
		}
		if j < stepMaxJ {
			t.Check(!FirstHitStepHolds(q, c, D, n, j+1))
		}
		return t
	}
	t.Check(RawPrefixUndivided(q, c, D, n, stepMaxJ))
	for i := 0; i <= stepMaxJ; i++ {
		t.Check(!Divides(D, AffineState(q, c, i, n)))
		t.Check(!Divides(D, RawIterate(q, c, D, n, i)))
		t.Check(!FirstHitStepHolds(q, c, D, n, i))
	}
	return t
}

// SweepQ checks one multiplier on the coefficient, divisor, seed and time grid.
func SweepQ(q int64) Totals {
	var t Totals
	for c := int64(-stepAbsCoeff); c <= stepAbsCoeff; c++ {
		for _, D := range stepDivisors {
			for n := int64(-stepAbsSeed); n <= stepAbsSeed; n++ {
				t.Add(CheckSeed(q, c, D, n))
			}
		}
	}
	return t
}

// SweepStep splits the multiplier range across workers and sums their totals.
func SweepStep() Totals {
	qs := make([]int64, 0, 2*stepAbsCoeff+1)
	for q := int64(-stepAbsCoeff); q <= stepAbsCoeff; q++ {
		qs = append(qs, q)
	}
	qs = qs[:len(qs)]
	parts := make([]Totals, len(qs))
	var wg sync.WaitGroup
	for worker := 0; worker < stepWorkers; worker++ {
		wg.Add(1)
		go func(worker int) {
			defer wg.Done()
			local := qs[:len(qs)]
			for i := worker; i < len(local); i += stepWorkers {
				parts[i] = SweepQ(local[i])
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

// main prints the number of comparisons and exits nonzero on a disagreement.
func main() {
	total := SweepStep()
	fmt.Printf("step checks: %d, failures: %d\n", total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
