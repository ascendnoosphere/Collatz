// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "fmt"

// Pow returns base^exp for a nonnegative exponent whose value fits in int64.
func Pow(base, exp int64) int64 {
	r := int64(1)
	for i := int64(0); i < exp; i++ {
		r *= base
	}
	return r
}

// Shortcut halves an even integer and sends an odd integer to (3n+1)/2.
func Shortcut(n int64) int64 {
	if n%2 == 0 {
		return n / 2
	}
	return (3*n + 1) / 2
}

// IterShortcut applies Shortcut exactly j times.
func IterShortcut(j, n int64) int64 {
	for i := int64(0); i < j; i++ {
		n = Shortcut(n)
	}
	return n
}

// OneCoeff returns 2^(a+3)-3^(a+1).
func OneCoeff(a int64) int64 {
	return Pow(2, a+3) - Pow(3, a+1)
}

// TwoCoeff returns 2^(a+2)-3^a.
func TwoCoeff(a int64) int64 {
	return Pow(2, a+2) - Pow(3, a)
}

// AcceptsPositiveTwo reports whether pred matches TwoCoeff positivity on 0..8.
func AcceptsPositiveTwo(pred func(a int64) bool) bool {
	for a := int64(0); a <= 8; a++ {
		if pred(a) != (TwoCoeff(a) > 0) {
			return false
		}
	}
	return true
}

// CheckGrid evaluates the one-excursion identities on a fixed finite rectangle.
// The returned count is the number of successful integer comparisons.
// A false ok means some comparison in that rectangle failed.
// The rectangle is not the theorem.
func CheckGrid() (int, bool) {
	count := 0
	for a := int64(0); a <= 12; a++ {
		one := OneCoeff(a)
		two := TwoCoeff(a)
		if (a <= 2) != (one > 0) || (a >= 3) != (one < 0) {
			return count, false
		}
		if (a <= 3) != (two > 0) || (a >= 4) != (two < 0) {
			return count, false
		}
		if OneCoeff(a) != TwoCoeff(a+1) {
			return count, false
		}
		if TwoCoeff(a+1) != 2*TwoCoeff(a)-Pow(3, a) {
			return count, false
		}
		count += 4
	}
	if TwoCoeff(0) != 3 || TwoCoeff(1) != 5 || TwoCoeff(2) != 7 {
		return count, false
	}
	if TwoCoeff(3) != 5 || TwoCoeff(4) != -17 {
		return count, false
	}
	count += 5
	for u := int64(3); u <= 31; u += 2 {
		if !(7 < OneCoeff(2)*u) || !(1 < TwoCoeff(2)*u) {
			return count, false
		}
		count++
	}
	for u := int64(1); u <= 31; u += 2 {
		if 7 < OneCoeff(3)*u || !(1 < TwoCoeff(3)*u) {
			return count, false
		}
		count++
	}
	for a := int64(4); a <= 8; a++ {
		for u := int64(1); u <= 21; u += 2 {
			if 7 < OneCoeff(a)*u || 1 < TwoCoeff(a)*u {
				return count, false
			}
			count++
		}
	}
	for a := int64(2); a <= 8; a++ {
		gap := 4*Pow(3, a) - 9*Pow(2, a)
		if gap < 0 {
			return count, false
		}
		count++
		for u := int64(1); u <= 25; u += 2 {
			x := Pow(2, a) * u
			w := Pow(3, a) * u
			if (w-1)%2 != 0 {
				return count, false
			}
			y := (w - 1) / 2
			left := 9*(x-1) + u*gap + 5
			if left != 8*y || 9*x > 8*(y+1) {
				return count, false
			}
			count++
		}
	}
	if Pow(9, 6) < 2*Pow(8, 6) || 2*Pow(8, 5) <= Pow(9, 5) {
		return count, false
	}
	count += 2
	n := int64(75)
	y := int64(2*n + 1)
	if 3*y+1 < 4*n || y-1 < 2*n || 2*y-1 < 3*n || y < 2*n {
		return count, false
	}
	count += 4
	if 4*19-1 != 75 || (9*19-1)/2 != 85 || (3*85+1)/4 != 64 || 64 >= 75 {
		return count, false
	}
	count += 4
	for a := int64(1); a <= 6; a++ {
		for u := int64(1); u <= 15; u += 2 {
			w := Pow(3, a) * u
			seed := Pow(2, a)*u - 1
			if w%4 == 3 {
				if IterShortcut(a+1, seed) != (w-1)/2 {
					return count, false
				}
				count++
			}
			residue := int64(1)
			if a%2 == 1 {
				residue = 3
			}
			if u%4 == residue {
				if (w-1)%4 != 0 {
					return count, false
				}
				m := (w - 1) / 4
				pred := Pow(2, a-1)*u - 1
				if IterShortcut(a+2, seed) != m || IterShortcut(a+1, pred) != m {
					return count, false
				}
				count++
			}
		}
	}
	return count, true
}

// main prints the number of successful finite-grid comparisons.
func main() {
	n, ok := CheckGrid()
	if !ok {
		fmt.Println(0)
		return
	}
	fmt.Println(n)
}
