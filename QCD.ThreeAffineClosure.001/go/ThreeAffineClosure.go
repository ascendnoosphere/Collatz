// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"fmt"
	"os"
)

const (
	// ExpMin is the smallest positive letter in the finite grid.
	ExpMin int64 = 1
	// ExpMax is the largest letter in the finite grid.
	ExpMax int64 = 5
	// QMin is the smallest positive multiplier in the finite grid.
	QMin int64 = 1
	// QMax is the largest multiplier in the finite grid.
	QMax int64 = 6
	// SeedMin is the least integer state in the finite grid.
	SeedMin int64 = -4
	// SeedMax is the greatest integer state in the finite grid.
	SeedMax int64 = 30
)

// Pow2 returns 2^n for a nonnegative exponent small enough for int64.
func Pow2(n int64) int64 {
	return int64(1) << n
}

// ClosureNumerator returns q^2 + q*2^a + 2^(a+b).
func ClosureNumerator(a, b, q int64) int64 {
	return q*q + q*Pow2(a) + Pow2(a+b)
}

// ThirdComponent returns q^2 + q*2^c + 2^(c+a).
func ThirdComponent(c, a, q int64) int64 {
	return q*q + q*Pow2(c) + Pow2(c+a)
}

// DeltaValue returns 2^(a+b+c) - q^3.
func DeltaValue(a, b, c, q int64) int64 {
	return Pow2(a+b+c) - q*q*q
}

// EquationsHold reports whether the three affine letters close on these states.
func EquationsHold(a, b, c, q, x, y, z int64) bool {
	if Pow2(a)*y != q*x+1 {
		return false
	}
	if Pow2(b)*z != q*y+1 {
		return false
	}
	return Pow2(c)*x == q*z+1
}

// IdentityHolds reports the divisibility consequence of a three-letter solution.
func IdentityHolds(a, b, c, q, x, y, z int64) bool {
	delta := DeltaValue(a, b, c, q)
	if delta == 0 {
		return false
	}
	numerator := ClosureNumerator(a, b, q)
	third := ThirdComponent(c, a, q)
	if delta*x != numerator || numerator%delta != 0 {
		return false
	}
	if delta*z != third || third%delta != 0 {
		return false
	}
	return z == third/delta
}

// ClosureHolds reports a grid point at which the equations and the identity hold.
func ClosureHolds(a, b, c, q, x, y, z int64) bool {
	return EquationsHold(a, b, c, q, x, y, z) &&
		IdentityHolds(a, b, c, q, x, y, z)
}

// ScanGrid counts finite checks. A failure is a solution that misses the identity.
func ScanGrid() (checks int, witnesses int, failures int) {
	var a, b, c, q, x, y, z int64
	for a = ExpMin; a <= ExpMax; a++ {
		for b = ExpMin; b <= ExpMax; b++ {
			for c = ExpMin; c <= ExpMax; c++ {
				for q = QMin; q <= QMax; q++ {
					for x = SeedMin; x <= SeedMax; x++ {
						for y = SeedMin; y <= SeedMax; y++ {
							for z = SeedMin; z <= SeedMax; z++ {
								checks++
								if !EquationsHold(a, b, c, q, x, y, z) {
									continue
								}
								witnesses++
								if !IdentityHolds(a, b, c, q, x, y, z) {
									failures++
								}
							}
						}
					}
				}
			}
		}
	}
	return checks, witnesses, failures
}

// GridSize is the number of points in the stated finite grid.
func GridSize() int {
	exp := int(ExpMax - ExpMin + 1)
	multipliers := int(QMax - QMin + 1)
	seeds := int(SeedMax - SeedMin + 1)
	return exp * exp * exp * multipliers * seeds * seeds * seeds
}

// main prints the number of grid checks and stops if the identity fails on one.
func main() {
	checks, _, failures := ScanGrid()
	fmt.Printf("checks %d\n", checks)
	if failures != 0 {
		fmt.Printf("failures %d\n", failures)
		os.Exit(1)
	}
}
