// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command FamilySplit checks the even-row parent identity on the grid 1..64.
// The printed count is the number of integers tested. It is not the theorem.
package main

import (
	"fmt"
	"os"
)

const (
	// GridLimit is the largest positive integer in the finite even-row grid.
	GridLimit = 64
)

// evenSourceWord is the single even letter of the even row.
var evenSourceWord = []bool{false}

// evenParentWord is the empty parent word of the even row.
var evenParentWord = []bool{}

// Shortcut halves an even value and sends an odd value to (3n+1)/2.
func Shortcut(n int) int {
	if n%2 == 0 {
		return n / 2
	}
	return (3*n + 1) / 2
}

// RunWord applies parity letters in order. False is the even letter.
func RunWord(word []bool, n int) int {
	for _, bit := range word {
		if bit {
			n = (3*n + 1) / 2
		} else {
			n = n / 2
		}
	}
	return n
}

// EvenSplitAt reports exact even-row membership for a positive integer.
// The half must be positive, strictly smaller, equal to the shortcut, and
// the common value of the source word and the empty parent word.
func EvenSplitAt(n int) bool {
	if n <= 1 || n%2 != 0 {
		return false
	}
	p := n / 2
	if p <= 0 || p >= n || 2*p != n || Shortcut(n) != p {
		return false
	}
	if RunWord(evenSourceWord, n) != p || RunWord(evenParentWord, p) != p {
		return false
	}
	return RunWord(evenSourceWord, n) == RunWord(evenParentWord, p)
}

// ConstantTruePredicate reports success for every input and ignores n.
func ConstantTruePredicate(n int) bool {
	return true
}

// PredicatesAgree reports whether pred and EvenSplitAt agree on 1..limit.
func PredicatesAgree(limit int, pred func(int) bool) bool {
	for n := 1; n <= limit; n++ {
		if pred(n) != EvenSplitAt(n) {
			return false
		}
	}
	return true
}

// CheckEvenSplit tests each integer from 1 through limit once.
// An even integer greater than 1 must have exact positive parent n/2.
// Every other integer in the grid must fail that exact doubling.
func CheckEvenSplit(limit int) (checks int, ok bool) {
	ok = true
	for n := 1; n <= limit; n++ {
		checks++
		p := n / 2
		if n > 1 && n%2 == 0 {
			source := RunWord(evenSourceWord, n)
			parent := RunWord(evenParentWord, p)
			if !(p > 0 && p < n && 2*p == n && Shortcut(n) == p &&
				source == p && parent == p && source == parent) {
				ok = false
			}
		} else if n > 1 && 2*p == n {
			ok = false
		}
	}
	return checks, ok
}

// main prints the number of grid checks, or stops when a check fails.
func main() {
	checks, ok := CheckEvenSplit(GridLimit)
	if !ok {
		fmt.Fprintln(os.Stderr, "even split grid failed")
		os.Exit(1)
	}
	fmt.Println(checks)
}
