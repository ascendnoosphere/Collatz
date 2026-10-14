// SPDX-License-Identifier: CC-BY-4.0
// ReverseBound checks the product obstruction and complementary factors exactly.
package main

import (
	"fmt"
	"sync"
)

const (
	MaxRank    = 12
	MinMu      = 2
	MaxMu      = 8
	ClosureMax = 4
	StateMax   = 8
	SlackMax   = 8
	SlackX     = 16
)

// PowerTwo rejects exponents whose powers cannot be represented in uint64.
func PowerTwo(e uint64) (uint64, bool) {
	if e >= 64 {
		return 0, false
	}
	return uint64(1) << e, true
}

// MultiplyChecked detects overflow before its result is used in a comparison.
func MultiplyChecked(a, b uint64) (uint64, bool) {
	if a == 0 || b == 0 {
		return 0, true
	}
	product := a * b
	if product/a != b {
		return 0, false
	}
	return product, true
}

// AddChecked distinguishes a represented sum from unsigned wraparound.
func AddChecked(a, b uint64) (uint64, bool) {
	sum := a + b
	return sum, sum >= a
}

// SubtractChecked rejects the negative differences excluded by the factor hypotheses.
func SubtractChecked(a, b uint64) (uint64, bool) {
	if a < b {
		return 0, false
	}
	return a - b, true
}

// SquareBelow reports q^2 < 2^(2t); the second result means the arithmetic is exact.
func SquareBelow(q, t uint64) (bool, bool) {
	if t >= 32 {
		return false, false
	}
	left, okL := MultiplyChecked(q, q)
	right, okR := PowerTwo(2 * t)
	if !okL || !okR {
		return false, false
	}
	return left < right, true
}

// ProductStrict reports (mu*q+1)^2 < mu^2*2^(2t), with checked arithmetic.
func ProductStrict(mu, q, t uint64) (bool, bool) {
	if t >= 32 {
		return false, false
	}
	mq, ok1 := MultiplyChecked(mu, q)
	left0, ok2 := AddChecked(mq, 1)
	left, ok3 := MultiplyChecked(left0, left0)
	mu2, ok4 := MultiplyChecked(mu, mu)
	power, ok5 := PowerTwo(2 * t)
	right, ok6 := MultiplyChecked(mu2, power)
	if !ok1 || !ok2 || !ok3 || !ok4 || !ok5 || !ok6 {
		return false, false
	}
	return left < right, true
}

// CeilingHolds checks mu*q+1 <= mu*2^t-1 within the integer square window.
func CeilingHolds(mu, q, t uint64) (bool, bool) {
	root, ok1 := PowerTwo(t)
	if !ok1 || q >= root {
		return false, false
	}
	mq, ok2 := MultiplyChecked(mu, q)
	left, ok3 := AddChecked(mq, 1)
	scaled, ok4 := MultiplyChecked(mu, root)
	right, ok5 := SubtractChecked(scaled, 1)
	if !ok2 || !ok3 || !ok4 || !ok5 {
		return false, false
	}
	return left <= right, true
}

// FactorHolds checks the product, sum and gap of the complementary factors.
func FactorHolds(m, q uint64) (bool, bool) {
	if m >= 32 {
		return false, false
	}
	root, ok1 := PowerTwo(m)
	power, ok2 := PowerTwo(2 * m)
	next, ok3 := PowerTwo(m + 1)
	if !ok1 || !ok2 || !ok3 || q > root {
		return false, false
	}
	qq, ok4 := MultiplyChecked(q, q)
	u, ok5 := SubtractChecked(root, q)
	v, ok6 := AddChecked(root, q)
	sum, ok7 := AddChecked(u, v)
	product, ok8 := MultiplyChecked(u, v)
	gap, ok9 := SubtractChecked(v, u)
	twice, ok10 := MultiplyChecked(2, q)
	restored, ok11 := AddChecked(product, qq)
	if !ok4 || !ok5 || !ok6 || !ok7 || !ok8 || !ok9 || !ok10 || !ok11 {
		return false, false
	}
	return sum == next && restored == power && gap == twice, true
}

// RecoverHolds includes the equal-factor boundary q=0 as well as positive gaps.
func RecoverHolds(m, u uint64) (bool, bool) {
	if m >= 32 {
		return false, false
	}
	root, ok1 := PowerTwo(m)
	next, ok2 := PowerTwo(m + 1)
	if !ok1 || !ok2 || u > root {
		return false, false
	}
	v, ok3 := SubtractChecked(next, u)
	gap, ok4 := SubtractChecked(v, u)
	if !ok3 || !ok4 {
		return false, false
	}
	if gap%2 != 0 {
		return false, true
	}
	return FactorHolds(m, gap/2)
}

// LettersHold tests the two equations, without counting absent premises as a closure.
func LettersHold(q, x, y, a, b uint64) (bool, bool) {
	pa, ok1 := PowerTwo(a)
	pb, ok2 := PowerTwo(b)
	qx, ok3 := MultiplyChecked(q, x)
	qy, ok4 := MultiplyChecked(q, y)
	leftA, ok5 := MultiplyChecked(pa, y)
	rightA, ok6 := AddChecked(qx, 1)
	leftB, ok7 := MultiplyChecked(pb, x)
	rightB, ok8 := AddChecked(qy, 1)
	if !ok1 || !ok2 || !ok3 || !ok4 || !ok5 || !ok6 || !ok7 || !ok8 {
		return false, false
	}
	return leftA == rightA && leftB == rightB, true
}

// ClosureAgrees accepts only present letters and verifies their substituted identity.
func ClosureAgrees(q, x, y, a, b uint64) (bool, bool) {
	present, known := LettersHold(q, x, y, a, b)
	if !known || !present {
		return false, false
	}
	k, ok1 := AddChecked(a, b)
	pk, ok2 := PowerTwo(k)
	pa, ok3 := PowerTwo(a)
	qq, ok4 := MultiplyChecked(q, q)
	middle, ok5 := MultiplyChecked(qq, x)
	offset, ok6 := AddChecked(q, pa)
	right, ok7 := AddChecked(middle, offset)
	left, ok8 := MultiplyChecked(pk, x)
	if !ok1 || !ok2 || !ok3 || !ok4 || !ok5 || !ok6 || !ok7 || !ok8 {
		return false, false
	}
	return left == right, true
}

// SlackHolds checks the exact nonnegative slack and its resulting inequality.
func SlackHolds(m, q, x uint64) (bool, bool) {
	if x < m {
		return false, false
	}
	qx, ok1 := MultiplyChecked(q, x)
	inner, ok2 := AddChecked(qx, 1)
	base, ok3 := MultiplyChecked(m, inner)
	gap, ok4 := SubtractChecked(x, m)
	left, ok5 := AddChecked(base, gap)
	mq, ok6 := MultiplyChecked(m, q)
	coefficient, ok7 := AddChecked(mq, 1)
	right, ok8 := MultiplyChecked(coefficient, x)
	if !ok1 || !ok2 || !ok3 || !ok4 || !ok5 || !ok6 || !ok7 || !ok8 {
		return false, false
	}
	return left == right && base <= right, true
}

// RecordCheck treats unknown arithmetic as a failure, not a successful comparison.
func RecordCheck(checks, failures *int, holds, known bool) {
	*checks++
	if !known || !holds {
		*failures++
	}
}

// ScanRank checks every multiplier in a rank, including even values and both endpoints.
func ScanRank(rank uint64) (checks, failures, sevenHits int) {
	if rank < 1 || rank > MaxRank {
		return 0, 1, 0
	}
	root, ok := PowerTwo(rank)
	RecordCheck(&checks, &failures, ok && root%2 == 0 && (root-1)%2 == 1, ok)
	for q := uint64(0); q <= root; q++ {
		below, known := SquareBelow(q, rank)
		RecordCheck(&checks, &failures, below == (q < root), known)
		good, known := FactorHolds(rank, q)
		RecordCheck(&checks, &failures, good, known)
		power, okP := PowerTwo(2 * rank)
		qq, okQ := MultiplyChecked(q, q)
		if okP && okQ && qq <= power && power-qq == 7 {
			sevenHits++
			RecordCheck(&checks, &failures, rank == 2 && q == 3, true)
		}
	}

	// The theorem's ceiling is checked for all candidates below the root, not just odd ones.
	for mu := uint64(MinMu); mu <= MaxMu; mu++ {
		for q := uint64(0); q < root; q++ {
			good, known := CeilingHolds(mu, q, rank)
			RecordCheck(&checks, &failures, good, known)
			good, known = ProductStrict(mu, q, rank)
			RecordCheck(&checks, &failures, good, known)
		}
	}
	for u := uint64(0); u <= root; u++ {
		good, known := RecoverHolds(rank, u)
		RecordCheck(&checks, &failures, good, known)
	}
	return checks, failures, sevenHits
}

// Scan combines independent rank checks with closure, slack and sharpness tests.
func Scan() (checks, failures, sevenHits int) {
	var rankChecks, rankFailures, rankHits [MaxRank]int
	var wait sync.WaitGroup

	// Each worker owns one fixed slot; only the final reduction reads other workers' totals.
	for rank := 0; rank < MaxRank; rank++ {
		wait.Add(1)
		go func(rank int) {
			defer wait.Done()
			rankChecks[rank], rankFailures[rank], rankHits[rank] = ScanRank(uint64(rank + 1))
		}(rank)
	}
	wait.Wait()
	for rank := 0; rank < MaxRank; rank++ {
		checks += rankChecks[rank]
		failures += rankFailures[rank]
		sevenHits += rankHits[rank]
	}

	// State 1 gives equality; state minimum 2 restores the strict defect.
	good, known := ProductStrict(1, 3, 2)
	RecordCheck(&checks, &failures, !good, known)
	good, known = ProductStrict(2, 3, 2)
	RecordCheck(&checks, &failures, good, known)
	good, known = RecoverHolds(0, 1)
	RecordCheck(&checks, &failures, good, known)

	// Only present letters are counted, including algebraic zero-division boundaries.
	for a := uint64(0); a <= ClosureMax; a++ {
		for b := uint64(0); b <= ClosureMax; b++ {
			for q := uint64(0); q <= StateMax; q++ {
				for x := uint64(1); x <= StateMax; x++ {
					for y := uint64(1); y <= StateMax; y++ {
						present, exact := LettersHold(q, x, y, a, b)
						if !exact {
							RecordCheck(&checks, &failures, false, false)
							continue
						}
						if !present {
							continue
						}
						good, known := ClosureAgrees(q, x, y, a, b)
						RecordCheck(&checks, &failures, good, known)
						allowed := x == 1 || y == 1 || (a+b)%2 != 0
						RecordCheck(&checks, &failures, allowed, true)
					}
				}
			}
		}
	}
	for m := uint64(0); m <= SlackMax; m++ {
		for q := uint64(0); q <= SlackMax; q++ {
			for x := m; x <= SlackX; x++ {
				good, known := SlackHolds(m, q, x)
				RecordCheck(&checks, &failures, good, known)
			}
		}
	}
	return checks, failures, sevenHits
}

// main reports exact finite checks; the unrestricted statements are proved in Lean.
func main() {
	checks, failures, sevenHits := Scan()
	fmt.Printf("checks=%d\nfailures=%d\nseven hits=%d\n", checks, failures, sevenHits)
	if failures != 0 {
		panic("an exact reverse-bound check failed")
	}
}
