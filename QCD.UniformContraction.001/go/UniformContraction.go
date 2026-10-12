// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"fmt"
	"os"
)

const (
	// HalfRadius is the radius used by the finite half-contraction grid.
	HalfRadius = 8
	// HalfLimit is the largest absolute seed checked for that grid.
	HalfLimit = 32
	// AffineAMax is the largest numerator slope in the affine grid.
	AffineAMax = 4
	// AffineDMax is the largest denominator in the affine grid.
	AffineDMax = 7
	// AffineBMax is the largest constant term in the affine grid.
	AffineBMax = 5
	// AffineNMax is the largest natural input in the affine grid.
	AffineNMax = 10
	// AffineHMax is the largest majorant iterate checked in the affine grid.
	AffineHMax = 5
)

// AbsInt returns the nonnegative absolute value of n.
func AbsInt(n int) int {
	if n < 0 {
		return -n
	}
	return n
}

// HalfOutside fixes every integer inside the radius and otherwise sends n to
// the truncating quotient n/2.
func HalfOutside(radius, n int) int {
	if AbsInt(n) <= radius {
		return n
	}
	return n / 2
}

// EntrySteps iterates step until the absolute value is at most radius.
// If that has not happened after AbsInt(seed) steps, entered is false.
func EntrySteps(radius, seed int, step func(int) int) (steps int, entered bool) {
	x := seed
	limit := AbsInt(seed)
	for AbsInt(x) > radius {
		if steps >= limit {
			return steps, false
		}
		x = step(x)
		steps++
	}
	return steps, true
}

// ContractionAt reports the half-contraction inequality at n.
// Inside the radius the inequality is not required.
func ContractionAt(radius, n int, step func(int) int) bool {
	if AbsInt(n) <= radius {
		return true
	}
	return 2*AbsInt(step(n)) <= AbsInt(n)
}

// ConstantTruePredicate ignores its input and reports success.
func ConstantTruePredicate(radius, n int, step func(int) int) bool {
	return true
}

// PredicatesAgree reports whether pred and ContractionAt have the same value
// at every integer from -limit through limit.
func PredicatesAgree(radius, limit int, step func(int) int,
	pred func(int, int, func(int) int) bool) bool {
	for n := -limit; n <= limit; n++ {
		if pred(radius, n, step) != ContractionAt(radius, n, step) {
			return false
		}
	}
	return true
}

// CheckHalf counts contraction tests outside the radius and entry tests for
// every seed from -limit through limit. The boolean is false when either test
// family fails.
func CheckHalf(radius, limit int, step func(int) int) (checks int, ok bool) {
	ok = true
	for n := -limit; n <= limit; n++ {
		if AbsInt(n) <= radius {
			continue
		}
		checks++
		if 2*AbsInt(step(n)) > AbsInt(n) {
			ok = false
		}
	}
	for seed := -limit; seed <= limit; seed++ {
		checks++
		steps, entered := EntrySteps(radius, seed, step)
		if !entered || steps > AbsInt(seed) {
			ok = false
		}
	}
	return checks, ok
}

// PowInt returns base raised to the nonnegative power exp.
// The value PowInt(0, 0) is 1, matching the empty product.
func PowInt(base, exp int) int {
	result := 1
	for i := 0; i < exp; i++ {
		result *= base
	}
	return result
}

// IterateMajorant iterates x |-> (a x + b) / d exactly, as the unreduced
// fraction num/den, starting from n/1.
func IterateMajorant(a, d, b, n, h int) (num, den int) {
	num = n
	den = 1
	for i := 0; i < h; i++ {
		num = a*num + b*den
		den = d * den
	}
	return num, den
}

// FormulaAgrees tests the cleared fixed-point iteration identity
// num (d - a) = a^h ((d - a) n - b) + d^h b.
func FormulaAgrees(a, d, b, n, h int) bool {
	num, _ := IterateMajorant(a, d, b, n, h)
	delta := d - a
	left := num * delta
	right := PowInt(a, h)*(delta*n-b) + PowInt(d, h)*b
	return left == right
}

// BudgetImplies tests the integer budget
// d^h ((N0+1)(d-a) - b) > a^h ((d-a)n - b),
// and, when the inequality holds, requires the iterated numerator to lie
// strictly below (N0+1) times the denominator.
func BudgetImplies(a, d, b, n, h int) bool {
	num, den := IterateMajorant(a, d, b, n, h)
	delta := d - a
	n0 := b / delta
	gap := (n0+1)*delta - b
	left := PowInt(d, h) * gap
	right := PowInt(a, h) * (delta*n - b)
	if left > right && num >= (n0+1)*den {
		return false
	}
	return true
}

// DecreaseAgrees tests equivalence of (d-a)n > b and a n + b < d n.
func DecreaseAgrees(a, d, b, n int) bool {
	delta := d - a
	return (delta*n > b) == (a*n+b < d*n)
}

// CoreHolds tests that n <= floor(b/(d-a)) implies a n + b < d (floor+1).
func CoreHolds(a, d, b, n int) bool {
	delta := d - a
	n0 := b / delta
	if n <= n0 && a*n+b >= d*(n0+1) {
		return false
	}
	return true
}

// HalfSlopeHolds tests that 2a < d and n > 2b imply 2(a n + b) < d n.
func HalfSlopeHolds(a, d, b, n int) bool {
	if 2*a < d && 2*b < n && 2*(a*n+b) >= d*n {
		return false
	}
	return true
}

// CheckAffine counts the decrease, core, half-slope, formula, and budget
// tests on the stated nonnegative box. The boolean is false if any test fails.
func CheckAffine() (checks int, ok bool) {
	ok = true
	for a := 0; a <= AffineAMax; a++ {
		for d := a + 1; d <= AffineDMax; d++ {
			for b := 0; b <= AffineBMax; b++ {
				for n := 0; n <= AffineNMax; n++ {
					checks++
					if !DecreaseAgrees(a, d, b, n) {
						ok = false
					}
					checks++
					if !CoreHolds(a, d, b, n) {
						ok = false
					}
					checks++
					if !HalfSlopeHolds(a, d, b, n) {
						ok = false
					}
					for h := 0; h <= AffineHMax; h++ {
						checks++
						if !FormulaAgrees(a, d, b, n, h) ||
							!BudgetImplies(a, d, b, n, h) {
							ok = false
						}
					}
				}
			}
		}
	}
	return checks, ok
}

// AffineCheckCount is the number of affine grid tests implied by the bounds.
func AffineCheckCount() int {
	count := 0
	for a := 0; a <= AffineAMax; a++ {
		for d := a + 1; d <= AffineDMax; d++ {
			for b := 0; b <= AffineBMax; b++ {
				for n := 0; n <= AffineNMax; n++ {
					count += 3
					count += AffineHMax + 1
				}
			}
		}
	}
	return count
}

// HalfCheckCount is the number of half-grid tests for the given bounds.
func HalfCheckCount(radius, limit int) int {
	outside := 0
	for n := -limit; n <= limit; n++ {
		if AbsInt(n) > radius {
			outside++
		}
	}
	return outside + 2*limit + 1
}

// main prints the number of finite integer checks. A failing check exits
// nonzero after that count. The grid is not the theorem.
func main() {
	halfStep := func(n int) int {
		return HalfOutside(HalfRadius, n)
	}
	halfChecks, halfOK := CheckHalf(HalfRadius, HalfLimit, halfStep)
	affineChecks, affineOK := CheckAffine()
	fmt.Printf("checks=%d\n", halfChecks+affineChecks)
	if !halfOK || !affineOK || halfChecks != HalfCheckCount(HalfRadius, HalfLimit) ||
		affineChecks != AffineCheckCount() {
		os.Exit(1)
	}
}
