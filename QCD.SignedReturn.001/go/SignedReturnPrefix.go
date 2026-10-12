// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnPrefix checks the division-free prefix identity on one
// finite grid. If no raw state before time j is divisible, the raw state at j
// equals q^j*n + c*U_j(q). The same comparison is made when the guard is read
// on affine states. Exact int64 arithmetic is used. The grid does not prove
// the identity for every integer parameter.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the finite check. Multipliers and offsets run through
// [-prefixAbsCoeff, prefixAbsCoeff], seeds through [-prefixAbsSeed,
// prefixAbsSeed], and times through 0..prefixMaxJ. The six divisors are
// prefixDivisors. On this rectangle every raw prefix of length at most 6 and
// every affine state satisfies
// |q|^j*|n| + |c|*sum_{i<j}|q|^i <= 4^6*8 + 4*(4^6-1)/3 = 38228,
// so no int64 multiplication overflows.
const (
	prefixAbsCoeff = 4
	prefixAbsSeed  = 8
	prefixMaxJ     = 6
	prefixWorkers  = 3
)

// prefixDivisors is the signed divisor list ±2, ±3, ±5.
var prefixDivisors = [6]int64{-5, -3, -2, 2, 3, 5}

// Totals counts comparisons and disagreements of one sweep.
type Totals struct {
	Checks   uint64
	Failures uint64
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

// powInt returns q^j for a nonnegative exponent on the stated grid.
func powInt(q int64, j int) int64 {
	out := int64(1)
	for i := 0; i < j; i++ {
		out *= q
	}
	return out
}

// trapSum returns U_j(q), the sum of q^0 through q^(j-1), with U_0(q) = 0.
func trapSum(q int64, j int) int64 {
	sum := int64(0)
	pow := int64(1)
	for i := 0; i < j; i++ {
		sum += pow
		pow *= q
	}
	return sum
}

// affineState returns q^j*n + c*U_j(q).
func affineState(q, c int64, j int, n int64) int64 {
	return powInt(q, j)*n + c*trapSum(q, j)
}

// rawStep applies one raw step. Go truncation toward zero is exact division
// when D divides n. D is never zero on the stated grid.
func rawStep(q, c, D, n int64) int64 {
	if n%D == 0 {
		return n / D
	}
	return q*n + c
}

// rawIterate returns the raw state at time j, including steps after a division.
func rawIterate(q, c, D, n int64, j int) int64 {
	cur := n
	for i := 0; i < j; i++ {
		cur = rawStep(q, c, D, cur)
	}
	return cur
}

// rawPrefixClean reports that D divides no raw state at a time i < j.
func rawPrefixClean(q, c, D, n int64, j int) bool {
	cur := n
	for i := 0; i < j; i++ {
		if cur%D == 0 {
			return false
		}
		cur = rawStep(q, c, D, cur)
	}
	return true
}

// affinePrefixClean reports that D divides no affine state at a time i < j.
func affinePrefixClean(q, c, D, n int64, j int) bool {
	for i := 0; i < j; i++ {
		if affineState(q, c, i, n)%D == 0 {
			return false
		}
	}
	return true
}

// PrefixAgrees is the forward identity. It is false when an earlier raw state
// is divisible, and false when the raw state differs from the affine state.
func PrefixAgrees(q, c, D, n int64, j int) bool {
	if !rawPrefixClean(q, c, D, n, j) {
		return false
	}
	return rawIterate(q, c, D, n, j) == affineState(q, c, j, n)
}

// AffinePrefixAgrees is the converse identity. It is false when an earlier
// affine state is divisible, and false when the two sides differ.
func AffinePrefixAgrees(q, c, D, n int64, j int) bool {
	if !affinePrefixClean(q, c, D, n, j) {
		return false
	}
	return rawIterate(q, c, D, n, j) == affineState(q, c, j, n)
}

// sweepQ checks one multiplier on the whole coefficient, divisor, seed, and
// time grid. Each cleanliness agreement and each applicable identity is a
// comparison. A prefix that has already divided is not an identity comparison.
func sweepQ(q int64) Totals {
	var t Totals
	for c := int64(-prefixAbsCoeff); c <= prefixAbsCoeff; c++ {
		for _, D := range prefixDivisors {
			for n := int64(-prefixAbsSeed); n <= prefixAbsSeed; n++ {
				for j := 0; j <= prefixMaxJ; j++ {
					rawClean := rawPrefixClean(q, c, D, n, j)
					affClean := affinePrefixClean(q, c, D, n, j)
					t.check(rawClean == affClean)
					if rawClean {
						t.check(PrefixAgrees(q, c, D, n, j))
					}
					if affClean {
						t.check(AffinePrefixAgrees(q, c, D, n, j))
					}
				}
			}
		}
	}
	return t
}

// sweepPrefix splits the multiplier range across workers and sums their totals.
func sweepPrefix() Totals {
	qs := make([]int64, 0, 2*prefixAbsCoeff+1)
	for q := int64(-prefixAbsCoeff); q <= prefixAbsCoeff; q++ {
		qs = append(qs, q)
	}
	parts := make([]Totals, len(qs))
	var wg sync.WaitGroup
	for worker := 0; worker < prefixWorkers; worker++ {
		wg.Add(1)
		go func(worker int) {
			defer wg.Done()
			for i := worker; i < len(qs); i += prefixWorkers {
				parts[i] = sweepQ(qs[i])
			}
		}(worker)
	}
	wg.Wait()
	var total Totals
	for _, part := range parts {
		total.add(part)
	}
	return total
}

// main prints the number of comparisons and exits nonzero on a disagreement.
func main() {
	total := sweepPrefix()
	fmt.Printf("prefix checks: %d, failures: %d\n", total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
