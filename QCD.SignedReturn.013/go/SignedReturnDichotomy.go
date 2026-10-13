// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnDichotomy classifies every seed of a finite grid as a
// first hit or a trap and checks that the two classifications agree. A first
// hit is the least time at which D divides the affine state. A trap is an
// orbit whose raw states at times 0 through |D|-1 are not divisible and whose
// residues repeat. Exact int64 arithmetic is used. The grid does not prove
// the equivalence for every integer parameter.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the finite check. Multipliers and offsets run through
// [-dichAbsQ, dichAbsQ] and [-dichAbsC, dichAbsC], seeds through
// [-dichAbsN, dichAbsN], and the divisors are dichDivisors. The decision
// scans times 0 through |D|-1, so the longest time is 4. On this rectangle
// |q|^j*|n| + |c|*sum_{i<j}|q|^i <= 3^4*6 + 3*(3^4-1)/2 = 606,
// and every raw branch is dominated by that pure affine majorant, so no
// int64 multiplication overflows.
const (
	dichAbsQ    = 3
	dichAbsC    = 3
	dichAbsN    = 6
	dichMaxM    = 5
	dichPerSeed = 4
	dichWorkers = 3
)

// dichDivisors is the signed divisor list ±2, ±3, ±5.
var dichDivisors = [6]int64{-5, -3, -2, 2, 3, 5}

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

// absInt returns the absolute value of a grid integer. The grid excludes
// the most negative int64, so the negation does not overflow.
func absInt(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
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
// when D divides n. The caller must not pass a zero divisor.
func rawStep(q, c, D, n int64) int64 {
	if n%D == 0 {
		return n / D
	}
	return q*n + c
}

// rawAt returns the raw state at time j. The time is the decision length.
func rawAt(q, c, D, n int64, j int) int64 {
	cur := n
	for i := 0; i < j; i++ {
		cur = rawStep(q, c, D, cur)
	}
	return cur
}

// modNorm returns the residue of n modulo m in 0..m-1. The modulus is positive.
func modNorm(n, m int64) int64 {
	r := n % m
	if r < 0 {
		r += m
	}
	return r
}

// leastRaw returns the least time in 0..|D|-1 at which D divides the raw
// state, or -1 when no such time exists. It returns -2 when |D| is outside
// the decision range, including D = 0.
func leastRaw(q, c, D, n int64) int {
	m := absInt(D)
	if D == 0 || m < 2 || m > dichMaxM {
		return -2
	}
	cur := n
	for j := 0; j < int(m); j++ {
		if cur%D == 0 {
			return j
		}
		if j+1 < int(m) {
			cur = rawStep(q, c, D, cur)
		}
	}
	return -1
}

// leastAffine returns the least time in 0..|D|-1 at which D divides the
// affine state, or -1 when no such time exists. It returns -2 when |D| is
// outside the decision range, including D = 0.
func leastAffine(q, c, D, n int64) int {
	m := absInt(D)
	if D == 0 || m < 2 || m > dichMaxM {
		return -2
	}
	for j := 0; j < int(m); j++ {
		if affineState(q, c, j, n)%D == 0 {
			return j
		}
	}
	return -1
}

// IsFirstHit reports that j is a first hit: D divides the affine state at j
// and at no earlier time. It is false for a nonpositive time, for D = 0, and
// for every time that is not the least affine division.
func IsFirstHit(q, c, D, n int64, j int) bool {
	if D == 0 || j < 0 {
		return false
	}
	if affineState(q, c, j, n)%D != 0 {
		return false
	}
	for i := 0; i < j; i++ {
		if affineState(q, c, i, n)%D == 0 {
			return false
		}
	}
	return true
}

// IsTrapped reports that the seed is trapped on the decision range. The raw
// states at times 0 through |D|-1 are not divisible by D, two of those
// residues agree, and each of those raw states equals the affine state. It
// is false when |D| is outside 2..dichMaxM, and false when a division occurs.
func IsTrapped(q, c, D, n int64) bool {
	m := absInt(D)
	if D == 0 || m < 2 || m > dichMaxM {
		return false
	}
	var res [dichMaxM]int64
	cur := n
	collision := false
	for i := 0; i < int(m); i++ {
		if cur%D == 0 || modNorm(cur, m) == 0 {
			return false
		}
		r := modNorm(cur, m)
		for k := 0; k < i; k++ {
			if res[k] == r {
				collision = true
			}
		}
		res[i] = r
		if affineState(q, c, i, n) != cur {
			return false
		}
		if i+1 < int(m) {
			cur = rawStep(q, c, D, cur)
		}
	}
	return collision
}

// ExistsHitIffNotTrapped reports that the least raw division time and the
// least affine division time agree, and that this common outcome is a first
// hit exactly when the seed is not trapped. It is false when |D| is outside
// 2..dichMaxM, so a constant-true replacement fails that input.
func ExistsHitIffNotTrapped(q, c, D, n int64) bool {
	m := absInt(D)
	if D == 0 || m < 2 || m > dichMaxM {
		return false
	}
	rawJ := leastRaw(q, c, D, n)
	affJ := leastAffine(q, c, D, n)
	if rawJ != affJ {
		return false
	}
	trapped := IsTrapped(q, c, D, n)
	if rawJ < 0 {
		return trapped
	}
	if trapped {
		return false
	}
	return IsFirstHit(q, c, D, n, rawJ)
}

// ExpectedChecks is the number of comparisons made by one full sweep.
func ExpectedChecks() uint64 {
	nQ := uint64(2*dichAbsQ + 1)
	nC := uint64(2*dichAbsC + 1)
	nN := uint64(2*dichAbsN + 1)
	nD := uint64(len(dichDivisors))
	return nQ * nC * nD * nN * dichPerSeed
}

// sweepQ checks one multiplier on the whole offset, divisor, and seed grid.
// Each seed contributes dichPerSeed comparisons: the two least times agree,
// trapping agrees with absence of a raw division, the first-hit predicate
// agrees with that time, and the equivalence predicate accepts the seed.
func sweepQ(q int64) Totals {
	var t Totals
	for c := int64(-dichAbsC); c <= dichAbsC; c++ {
		for _, D := range dichDivisors {
			for n := int64(-dichAbsN); n <= dichAbsN; n++ {
				rawJ := leastRaw(q, c, D, n)
				affJ := leastAffine(q, c, D, n)
				t.check(rawJ == affJ)
				t.check(IsTrapped(q, c, D, n) == (rawJ < 0))
				if rawJ < 0 {
					t.check(!IsFirstHit(q, c, D, n, 0))
				} else {
					t.check(IsFirstHit(q, c, D, n, rawJ))
				}
				t.check(ExistsHitIffNotTrapped(q, c, D, n))
			}
		}
	}
	return t
}

// sweepDichotomy splits the multiplier range across workers and sums totals.
func sweepDichotomy() Totals {
	nQ := 2*dichAbsQ + 1
	qs := make([]int64, 0, nQ)
	for q := int64(-dichAbsQ); q <= dichAbsQ; q++ {
		qs = append(qs, q)
	}
	parts := make([]Totals, len(qs))
	var wg sync.WaitGroup
	for worker := 0; worker < dichWorkers; worker++ {
		wg.Add(1)
		go func(worker int) {
			defer wg.Done()
			for i := worker; i < len(qs); i += dichWorkers {
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
	total := sweepDichotomy()
	fmt.Printf("dichotomy checks: %d, failures: %d\n", total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
