// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnImmediate checks the exponent-zero return on one finite
// grid. Time zero is a first hit exactly when the divisor divides the seed,
// because the earlier-time range is empty. If the divisor divides the seed,
// the quotient multiplies back in absolute value, and the core comparison
// holds with slope 1 and constant 0. Exact int64 arithmetic is used. The grid
// does not prove these statements for every integer.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the exact grid. Seeds run through [-30, 30]. The six signed
// divisors are ±2, ±3, ±5. Time-zero affine states are also compared with the
// seed for multipliers in {-2, 0, 2} and offsets in {-3, 0, 4}. Every product
// below has absolute value at most 5*30 = 150, so it fits in an int64.
const (
	seedMin          = int64(-30)
	seedMax          = int64(30)
	immediateWorkers = 4
)

// signedDivisors is the list ±2, ±3, ±5.
var signedDivisors = [6]int64{-5, -3, -2, 2, 3, 5}

// zeroMultipliers are the multipliers used to test the empty power q^0 = 1.
var zeroMultipliers = [3]int64{-2, 0, 2}

// zeroOffsets are the offsets used to test the empty sum multiplied by c.
var zeroOffsets = [3]int64{-3, 0, 4}

// Totals counts comparisons and disagreements of one sweep.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// Workspace holds the time-zero power and offset sum for one pair (q, c).
// A workspace is not safe for concurrent calls. The caller reuses it.
type Workspace struct {
	Pow  int64
	Trap int64
	Q    int64
	C    int64
}

// Cache holds the six signed divisors. After construction it is read only.
type Cache struct {
	Divisors [6]int64
}

// NewWorkspace returns an empty power-and-sum workspace.
func NewWorkspace() *Workspace {
	return &Workspace{}
}

// NewCache returns the six signed divisors ±2, ±3, ±5.
func NewCache() *Cache {
	return &Cache{Divisors: signedDivisors}
}

// check records one comparison.
func (t *Totals) check(ok bool) {
	t.Checks++
	if !ok {
		t.Failures++
	}
}

// add accumulates a worker total into the receiver.
func (t *Totals) add(other Totals) {
	t.Checks += other.Checks
	t.Failures += other.Failures
}

// abs64 returns the absolute value. Every call site uses a value whose
// negation still fits in an int64.
func abs64(x int64) int64 {
	if x < 0 {
		return -x
	}
	return x
}

// Divides reports that D divides n. The caller passes a nonzero divisor.
// Truncation toward zero makes a zero remainder the divisibility test.
func Divides(D, n int64) bool {
	return n%D == 0
}

// Prepare stores q^j and the sum of q^0 through q^(j-1). At j = 0 both loops
// are empty, so the power is 1 and the offset sum is 0, including q = 0.
func (w *Workspace) Prepare(q, c int64, j int) {
	pow := int64(1)
	trap := int64(0)
	for i := 0; i < j; i++ {
		trap += pow
		pow *= q
	}
	w.Pow = pow
	w.Trap = trap
	w.Q = q
	w.C = c
}

// Affine returns q^j*n + c*U_j(q) from the prepared power and offset sum.
func (w *Workspace) Affine(n int64) int64 {
	return w.Pow*n + w.C*w.Trap
}

// AffineAtZero returns q^0*n + c*U_0(q). Both loops in Prepare stop before
// the first index, so the value equals n for every q and c.
func AffineAtZero(q, c, n int64) int64 {
	var w Workspace
	w.Prepare(q, c, 0)
	return w.Affine(n)
}

// RangeNonempty reports that some natural number is strictly less than j.
// At j = 0 the counted range is empty, so the earlier-time quantifier has
// no witness.
func RangeNonempty(j int) bool {
	i := 0
	for i < j {
		i++
	}
	return i != 0
}

// FirstHitAtZero reports that time 0 is a first hit of n by D. Divisibility
// is read on the time-zero affine state, and the earlier-time range is empty.
func FirstHitAtZero(D, n int64) bool {
	return Divides(D, AffineAtZero(0, 0, n)) && !RangeNonempty(0)
}

// ImmediateReturn is the raw division n/D. The caller passes a nonzero
// divisor. When D divides n this is the raw step.
func ImmediateReturn(D, n int64) int64 {
	return n / D
}

// AbsProductExact reports |D| * |n/D| = |n| under truncation toward zero.
func AbsProductExact(D, n int64) bool {
	return abs64(D)*abs64(n/D) == abs64(n)
}

// CoreHolds reports A < |D| and |D| * |n/D| ≤ A*|n| + B. A zero divisor
// fails the strict inequality and is not used as a quotient.
func CoreHolds(A, B, D, n int64) bool {
	m := abs64(D)
	if m == 0 {
		return false
	}
	return A < m && m*abs64(n/D) <= A*abs64(n)+B
}

// sweepSeeds checks every seed from lo through hi against the cached divisors.
func sweepSeeds(lo, hi int64, divs *[6]int64, w *Workspace) Totals {
	var total Totals
	for n := lo; n <= hi; n++ {
		for _, q := range zeroMultipliers {
			for _, c := range zeroOffsets {
				w.Prepare(q, c, 0)
				total.check(w.Affine(n) == n)
			}
		}
		for _, D := range divs {
			hit := FirstHitAtZero(D, n)
			div := Divides(D, n)
			total.check(hit == div)
			if div {
				quot := ImmediateReturn(D, n)
				total.check(D*quot == n)
				total.check(AbsProductExact(D, n))
				total.check(CoreHolds(1, 0, D, n))
			} else {
				total.check(!AbsProductExact(D, n))
			}
		}
	}
	return total
}

// RunSweep checks every seed from seedMin through seedMax on four chunks.
func RunSweep(cache *Cache) Totals {
	span := int(seedMax - seedMin + 1)
	width := span / immediateWorkers
	extra := span % immediateWorkers
	chunks := make([]Totals, immediateWorkers)
	var wg sync.WaitGroup
	start := seedMin
	for i := 0; i < immediateWorkers; i++ {
		length := width
		if i < extra {
			length++
		}
		lo := start
		hi := start + int64(length) - 1
		start = hi + 1
		wg.Add(1)
		go func(idx int, lo, hi int64) {
			defer wg.Done()
			w := NewWorkspace()
			chunks[idx] = sweepSeeds(lo, hi, &cache.Divisors, w)
		}(i, lo, hi)
	}
	wg.Wait()
	var total Totals
	for i := 0; i < immediateWorkers; i++ {
		total.add(chunks[i])
	}
	return total
}

// main prints the number of exact comparisons and exits nonzero on disagreement.
func main() {
	cache := NewCache()
	total := RunSweep(cache)
	fmt.Printf("immediate return checks: %d, failures: %d\n",
		total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
