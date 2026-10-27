// Copyright (c) 2026 ascendnoosphere
// SPDX-License-Identifier: CC-BY-4.0

// Exact integer checks of the repunit divisibility identity on five cells.
// The cells are (q, c, D, k) = (2, 1, 3, 2), (2, 1, 7, 3), (2, 1, 15, 4),
// (3, 1, 4, 2), and (3, 1, 13, 3). Each comparison is an integer identity.
// These rows do not replace the induction for a general base.
package main

import (
	"fmt"
	"os"
	"sync"
)

// displayedChecks counts the comparisons on the five cells: five arithmetic
// facts on each cell, and two affine facts on every residue. The residue
// counts are 3, 7, 15, 4, and 13, so the total is 5*5 + 2*42 = 109.
const displayedChecks = 109

// Cell is one displayed parameter tuple (q, c, D, k).
type Cell struct {
	Q uint64
	C uint64
	D uint64
	K uint64
}

// Cache holds the five displayed cells.
type Cache struct {
	Cells [5]Cell
}

// Workspace stores the current affine state for one residue walk.
type Workspace struct {
	State uint64
}

// Totals accumulates comparison counts.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// NewWorkspace returns a zero affine state.
func NewWorkspace() *Workspace {
	return &Workspace{}
}

// DisplayedCache returns the five cells on which the identity is checked.
func DisplayedCache() Cache {
	return Cache{Cells: [5]Cell{
		{Q: 2, C: 1, D: 3, K: 2},
		{Q: 2, C: 1, D: 7, K: 3},
		{Q: 2, C: 1, D: 15, K: 4},
		{Q: 3, C: 1, D: 4, K: 2},
		{Q: 3, C: 1, D: 13, K: 3},
	}}
}

// Record stores one boolean comparison.
func (t *Totals) Record(ok bool) {
	t.Checks++
	if !ok {
		t.Failures++
	}
}

// Add returns a+b, or false when the sum does not fit in uint64.
func Add(a, b uint64) (uint64, bool) {
	sum := a + b
	if sum < a {
		return 0, false
	}
	return sum, true
}

// Mul returns a*b, or false when the product does not fit in uint64.
func Mul(a, b uint64) (uint64, bool) {
	if a != 0 && b > ^uint64(0)/a {
		return 0, false
	}
	return a * b, true
}

// Gcd returns the nonnegative greatest common divisor of a and b.
func Gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// Pow returns q^k, or false when the power does not fit in uint64.
func Pow(q, k uint64) (uint64, bool) {
	acc := uint64(1)
	base := q
	exp := k
	for exp > 0 {
		if exp&1 == 1 {
			next, ok := Mul(acc, base)
			if !ok {
				return 0, false
			}
			acc = next
		}
		exp >>= 1
		if exp == 0 {
			break
		}
		next, ok := Mul(base, base)
		if !ok {
			return 0, false
		}
		base = next
	}
	return acc, true
}

// RepunitSum returns 1+q+...+q^(k-1). The boolean is false on overflow.
func RepunitSum(q, k uint64) (uint64, bool) {
	var sum uint64
	pow := uint64(1)
	var i uint64
	for i = 0; i < k; i++ {
		next, ok := Add(sum, pow)
		if !ok {
			return 0, false
		}
		sum = next
		if i+1 < k {
			pow, ok = Mul(pow, q)
			if !ok {
				return 0, false
			}
		}
	}
	return sum, true
}

// Walk stores the k-fold image of r under x |-> q*x+c. It reports overflow.
func (w *Workspace) Walk(q, c, k, r uint64) bool {
	w.State = r
	var j uint64
	for j = 0; j < k; j++ {
		prod, ok := Mul(q, w.State)
		if !ok {
			return false
		}
		next, ok := Add(prod, c)
		if !ok {
			return false
		}
		w.State = next
	}
	return true
}

// DivisorFacts compares the five arithmetic parts of the divisibility identity.
func DivisorFacts(q, k, D uint64) (bool, bool, bool, bool, bool, uint64, uint64) {
	sum, sumFit := RepunitSum(q, k)
	sumOK := sumFit && sum == D
	pow, powFit := Pow(q, k)
	var prod uint64
	prodFit := false
	if q >= 1 {
		prod, prodFit = Mul(q-1, D)
	}
	var next uint64
	nextFit := false
	if prodFit {
		next, nextFit = Add(prod, 1)
	}
	geomOK := powFit && nextFit && pow == next
	dvdOK := powFit && pow >= 1 && D != 0 && (pow-1)%D == 0
	modOK := q != 0 && D%q == 1
	coprimeOK := Gcd(q, D) == 1
	return sumOK, geomOK, dvdOK, modOK, coprimeOK, pow, sum
}

// AffineFacts reports whether the closed form and the residue return hold.
func AffineFacts(q, c, k, D, r, pow, sum uint64, arithOK bool, w *Workspace) (bool, bool) {
	if !arithOK || D == 0 || !w.Walk(q, c, k, r) {
		return false, false
	}
	pr, ok1 := Mul(pow, r)
	cs, ok2 := Mul(c, sum)
	closed, ok3 := Add(pr, cs)
	if !ok1 || !ok2 || !ok3 {
		return false, false
	}
	return w.State == closed, w.State%D == r%D
}

// IdentityHolds reports the full divisibility and return package for one cell.
func IdentityHolds(q, k, c, D uint64) bool {
	sumOK, geomOK, dvdOK, modOK, coprimeOK, pow, sum := DivisorFacts(q, k, D)
	if !(sumOK && geomOK && dvdOK && modOK && coprimeOK) || D == 0 {
		return false
	}
	w := NewWorkspace()
	var r uint64
	for r = 0; r < D; r++ {
		form, cong := AffineFacts(q, c, k, D, r, pow, sum, true, w)
		if !form || !cong {
			return false
		}
	}
	return true
}

// CheckCell counts the arithmetic facts and both affine facts on one cell.
func CheckCell(cell Cell, w *Workspace) Totals {
	var totals Totals
	sumOK, geomOK, dvdOK, modOK, coprimeOK, pow, sum := DivisorFacts(cell.Q, cell.K, cell.D)
	totals.Record(sumOK)
	totals.Record(geomOK)
	totals.Record(dvdOK)
	totals.Record(modOK)
	totals.Record(coprimeOK)
	arithOK := sumOK && geomOK && dvdOK && modOK && coprimeOK
	if cell.D == 0 {
		return totals
	}
	var r uint64
	for r = 0; r < cell.D; r++ {
		form, cong := AffineFacts(cell.Q, cell.C, cell.K, cell.D, r, pow, sum, arithOK, w)
		totals.Record(form)
		totals.Record(cong)
	}
	return totals
}

// CheckDisplayed checks the five cached cells independently.
func CheckDisplayed(cache Cache) Totals {
	cells := cache.Cells[:]
	cells = cells[:len(cells)]
	n := len(cells)
	parts := make([]Totals, n)
	var wg sync.WaitGroup
	var i int
	for i = 0; i < n; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			parts[i] = CheckCell(cells[i], NewWorkspace())
		}(i)
	}
	wg.Wait()
	var totals Totals
	parts = parts[:len(parts)]
	for i = 0; i < len(parts); i++ {
		totals.Checks += parts[i].Checks
		totals.Failures += parts[i].Failures
	}
	return totals
}

// main prints the number of integer comparisons on the displayed cells.
func main() {
	totals := CheckDisplayed(DisplayedCache())
	fmt.Printf("checks %d\n", totals.Checks)
	if totals.Failures != 0 || totals.Checks != displayedChecks {
		os.Exit(1)
	}
}
