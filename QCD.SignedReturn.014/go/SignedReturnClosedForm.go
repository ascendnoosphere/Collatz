// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnClosedForm prints the offset sum on the rectangle
// q in [-6, 6] and j in 0..8, and checks two finite predictions there.
// For q ≥ 2 it checks the exact nonnegative quotient (q^j-1)/(q-1).
// For |q| ≥ 2 it checks (|q|-1)*|U_j(q)| ≤ |q|^j-1.
// Exact int64 arithmetic is used. On this rectangle |q|^j ≤ 6^8 = 1679616,
// so every product below stays inside int64. The grid does not prove the
// identities for every integer.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the finite check. Multipliers run from gridQMin through gridQMax
// and times run from 0 through gridMaxJ. Three workers split the multipliers.
const (
	gridQMin    = -6
	gridQMax    = 6
	gridMaxJ    = 8
	gridWorkers = 3
)

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

// PowInt returns q^j by repeated multiplication. The exponent is nonnegative.
func PowInt(q int64, j int) int64 {
	out := int64(1)
	for i := 0; i < j; i++ {
		out *= q
	}
	return out
}

// TrapSum returns U_j(q), with U_0(q) = 0 and U_{j+1}(q) = q*U_j(q)+1.
func TrapSum(q int64, j int) int64 {
	sum := int64(0)
	for i := 0; i < j; i++ {
		sum = q*sum + 1
	}
	return sum
}

// Abs64 returns the absolute value. The stated grid never meets MinInt64.
func Abs64(n int64) int64 {
	if n < 0 {
		return -n
	}
	return n
}

// PositiveClosedFormHolds is the exact nonnegative quotient for q ≥ 2.
// It returns false for every q < 2, including the signed quotient at q = -2.
// A replacement that returns true on every input is therefore rejected.
func PositiveClosedFormHolds(q int64, j int) bool {
	if q < 2 {
		return false
	}
	sum := TrapSum(q, j)
	pow := PowInt(q, j)
	if sum < 0 {
		return false
	}
	den := q - 1
	num := pow - 1
	if num%den != 0 {
		return false
	}
	return (q-1)*sum == num && sum == num/den
}

// GeometricAbsHolds is the bound (|q|-1)*|U_j(q)| ≤ |q|^j-1 for |q| ≥ 2.
// It returns false when |q| < 2, so a constant-true replacement is rejected.
func GeometricAbsHolds(q int64, j int) bool {
	r := Abs64(q)
	if r < 2 {
		return false
	}
	pow := PowInt(r, j)
	return (r-1)*Abs64(TrapSum(q, j)) <= pow-1
}

// PositiveRepunitEqualsAbs is the false formula |U_j(q)| = (|q|^j-1)/(|q|-1).
// It is a negative control, not a claimed identity.
func PositiveRepunitEqualsAbs(q int64, j int) bool {
	r := Abs64(q)
	if r < 2 {
		return false
	}
	pow := PowInt(r, j)
	den := r - 1
	if (pow-1)%den != 0 {
		return false
	}
	return Abs64(TrapSum(q, j)) == (pow-1)/den
}

// SweepQ checks one multiplier at every time up to gridMaxJ.
// The positive quotient is tested only for q ≥ 2. The absolute bound is
// tested only for |q| ≥ 2. Below those thresholds the predicates must refuse.
func SweepQ(q int64) Totals {
	var t Totals
	for j := 0; j <= gridMaxJ; j++ {
		if q >= 2 {
			t.Check(PositiveClosedFormHolds(q, j))
		} else {
			t.Check(!PositiveClosedFormHolds(q, j))
		}
		if Abs64(q) >= 2 {
			t.Check(GeometricAbsHolds(q, j))
		} else {
			t.Check(!GeometricAbsHolds(q, j))
		}
	}
	return t
}

// SweepClosedForm splits the multiplier range across workers.
func SweepClosedForm() Totals {
	qs := make([]int64, 0, gridQMax-gridQMin+1)
	for q := int64(gridQMin); q <= gridQMax; q++ {
		qs = append(qs, q)
	}
	parts := make([]Totals, len(qs))
	var wg sync.WaitGroup
	for worker := 0; worker < gridWorkers; worker++ {
		wg.Add(1)
		go func(worker int) {
			defer wg.Done()
			for i := worker; i < len(qs); i += gridWorkers {
				parts[i] = SweepQ(qs[i])
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

// PrintTrapSums writes U_j(q) for every multiplier and time on the grid.
func PrintTrapSums() {
	for q := int64(gridQMin); q <= gridQMax; q++ {
		for j := 0; j <= gridMaxJ; j++ {
			fmt.Printf("trap q=%d j=%d sum=%d\n", q, j, TrapSum(q, j))
		}
	}
}

// main prints the offset sums, the hand check at q=-2 and j=2, and the count.
func main() {
	PrintTrapSums()
	sum := TrapSum(-2, 2)
	signed := (PowInt(-2, 2) - 1) / ((-2) - 1)
	repunit := (PowInt(2, 2) - 1) / (2 - 1)
	fmt.Printf("neg-two check: sum=%d signedQuotient=%d positiveRepunit=%d\n",
		sum, signed, repunit)
	total := SweepClosedForm()
	fmt.Printf("closed-form checks: %d, failures: %d\n",
		total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
