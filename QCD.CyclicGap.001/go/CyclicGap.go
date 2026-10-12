// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"fmt"
	"os"
)

const (
	// GridMax is the largest block length in the two-run grid.
	GridMax = 8
	// RotMax is the largest block length in the three-run grid.
	RotMax = 3
	// PowBound is the length of the cached powers of two and three.
	PowBound = 40
	// WordBound is the capacity of the rotation buffers.
	WordBound = 24
)

// Cache stores powers of two and three through exponent PowBound-1.
type Cache struct {
	Pow2 [PowBound]int
	Pow3 [PowBound]int
}

// Workspace holds one word and one rotation.
type Workspace struct {
	Left  [WordBound]int
	Right [WordBound]int
}

// AbsInt returns the nonnegative absolute value of n.
func AbsInt(n int) int {
	if n < 0 {
		return -n
	}
	return n
}

// FillCache writes 2^i and 3^i into c.
func FillCache(c *Cache) {
	p2 := c.Pow2[:len(c.Pow2)]
	p3 := c.Pow3[:len(c.Pow3)]
	p2[0] = 1
	p3[0] = 1
	for i := 1; i < len(p2); i++ {
		p2[i] = p2[i-1] * 2
		p3[i] = p3[i-1] * 3
	}
}

// Divides reports whether d divides b, using the absolute value of d.
func Divides(d, b int) bool {
	a := AbsInt(d)
	if a == 0 {
		return false
	}
	return b%a == 0
}

// AccB is the accelerated numerator of word at the given shift.
func AccB(c *Cache, shift int, word []int) int {
	w := word[:len(word)]
	n := len(w)
	b := 0
	s := shift
	for i := 0; i < n; i++ {
		b += c.Pow3[n-1-i] * c.Pow2[s]
		s += w[i]
	}
	return b
}

// ConstantTrue accepts every pair. It is not the gap.
func ConstantTrue(p, q int) bool {
	return true
}

// StrictPositiveGap is the positive normalized bound.
// It fails for some pairs, including (1,1).
func StrictPositiveGap(c *Cache, p, q int) bool {
	qPow := c.Pow2[p+2*q]
	pPow := c.Pow3[p+q]
	if qPow <= pPow {
		return false
	}
	return (qPow-pPow)*c.Pow3[q] < pPow
}

// ExpectedCheckCount is the number of comparisons in CheckGrid.
func ExpectedCheckCount() int {
	pairs := GridMax * GridMax
	small := GridMax * 2
	ones := GridMax
	twos := GridMax * 3
	letter := 1
	rot := RotMax * RotMax * RotMax * 2
	return pairs*3 + small + ones + twos + letter + rot
}

// FillThree writes 1^p 2^q 1^s into dst and returns the length.
func FillThree(dst []int, p, q, s int) int {
	n := 0
	for i := 0; i < p; i++ {
		dst[n] = 1
		n++
	}
	for i := 0; i < q; i++ {
		dst[n] = 2
		n++
	}
	for i := 0; i < s; i++ {
		dst[n] = 1
		n++
	}
	return n
}

// RotateLeft writes the left rotation of src by k places into dst.
func RotateLeft(dst, src []int, n, k int) {
	d := dst[:n]
	s := src[:n]
	for i := 0; i < n; i++ {
		d[i] = s[(i+k)%n]
	}
}

// ExponentSum adds the entries of word.
func ExponentSum(word []int) int {
	w := word[:len(word)]
	sum := 0
	for i := 0; i < len(w); i++ {
		sum += w[i]
	}
	return sum
}

// CheckGrid checks the two-run identities, the small-second-block
// exclusion, the constant words, and the three-run rotation on a
// finite rectangle. The rectangle is not the theorem.
func CheckGrid() (int, bool) {
	var c Cache
	var w Workspace
	FillCache(&c)
	checks := 0
	ok := true
	for p := 1; p <= GridMax; p++ {
		for q := 1; q <= GridMax; q++ {
			word := w.Left[:p+q]
			for i := 0; i < p; i++ {
				word[i] = 1
			}
			for i := 0; i < q; i++ {
				word[p+i] = 2
			}
			b := AccB(&c, 0, word)
			left := b + c.Pow2[p+1]*c.Pow3[q]
			right := c.Pow3[p+q] + c.Pow2[p+2*q]
			checks++
			if left != right {
				ok = false
			}
			qPow := c.Pow2[p+2*q]
			pPow := c.Pow3[p+q]
			diff := b - (qPow - pPow)
			want := 2 * c.Pow3[q] * (c.Pow3[p] - c.Pow2[p])
			checks++
			if diff != want {
				ok = false
			}
			checks++
			if qPow > pPow && Divides(qPow-pPow, b) {
				n := qPow - pPow
				gap := c.Pow3[p] - c.Pow2[p]
				if n <= 0 || gap%n != 0 || n*c.Pow3[q] >= pPow {
					ok = false
				}
			}
			if q <= 2 {
				checks++
				if qPow > pPow && Divides(qPow-pPow, b) {
					ok = false
				}
			}
		}
	}
	for p := 1; p <= GridMax; p++ {
		checks++
		if c.Pow2[p] >= c.Pow3[p] {
			ok = false
		}
	}
	for q := 1; q <= GridMax; q++ {
		word := w.Left[:q]
		for i := 0; i < q; i++ {
			word[i] = 2
		}
		b := AccB(&c, 0, word)
		checks++
		if b != c.Pow2[2*q]-c.Pow3[q] {
			ok = false
		}
		checks++
		if c.Pow2[2*q] != c.Pow3[q]+b {
			ok = false
		}
		checks++
		if c.Pow3[q] >= c.Pow2[2*q] {
			ok = false
		}
	}
	checks++
	if 4*1 != 3*1+1 {
		ok = false
	}
	for p := 1; p <= RotMax; p++ {
		for q := 1; q <= RotMax; q++ {
			for s := 1; s <= RotMax; s++ {
				n := FillThree(w.Left[:], p, q, s)
				RotateLeft(w.Right[:], w.Left[:], n, p+q)
				checks++
				match := true
				for i := 0; i < p+s; i++ {
					if w.Right[i] != 1 {
						match = false
					}
				}
				for i := 0; i < q; i++ {
					if w.Right[p+s+i] != 2 {
						match = false
					}
				}
				if !match {
					ok = false
				}
				b0 := AccB(&c, 0, w.Left[:n])
				b1 := AccB(&c, 0, w.Right[:n])
				sum := ExponentSum(w.Left[:n])
				delta := c.Pow2[sum] - c.Pow3[n]
				checks++
				if Divides(delta, b0) != Divides(delta, b1) {
					ok = false
				}
			}
		}
	}
	return checks, ok
}

// main prints the number of finite checks. The grid is not the theorem.
func main() {
	checks, ok := CheckGrid()
	if !ok {
		fmt.Fprintln(os.Stderr, "grid check failed")
		os.Exit(1)
	}
	fmt.Println(checks)
}
