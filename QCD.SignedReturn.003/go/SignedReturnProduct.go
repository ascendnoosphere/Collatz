// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnProduct checks the exact division identities on one
// finite signed grid. If D is nonzero and D divides a, then D*(a/D) = a and
// |D|*|a/D| = |a|. A nonzero remainder is a rejection, not a rounded
// quotient. Agreement on the grid does not prove the identities for every
// integer.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the exact grid. Divisors run through the nonzero integers of
// absolute value at most productAbsD, and states through every integer of
// absolute value at most productAbsA. Every product below has absolute value
// at most 12*36 = 432, so the arithmetic stays inside int64. The zero divisor
// is excluded. math.MinInt64 is not in the grid, so negation of a negative
// value does not overflow.
const (
	productAbsD    = 12
	productAbsA    = 36
	productWorkers = 4
)

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

// absInt returns the absolute value of an integer on the stated grid.
func absInt(x int64) int64 {
	if x < 0 {
		return -x
	}
	return x
}

// Workspace stores one divisor, one state, and the truncating quotient.
// Load reuses the struct. A workspace is not safe for concurrent calls.
type Workspace struct {
	D     int64
	A     int64
	Quot  int64
	Exact bool
}

// NewWorkspace returns an empty divisor-state workspace.
func NewWorkspace() *Workspace {
	return &Workspace{}
}

// Load stores D and a. When D is zero or the remainder is nonzero, Exact is
// false and Quot is left at zero. No rounded quotient is stored. Division and
// remainder are evaluated only for D ≠ 0, and both truncate toward zero.
func (w *Workspace) Load(D, a int64) {
	w.D = D
	w.A = a
	w.Quot = 0
	w.Exact = false
	if D == 0 {
		return
	}
	if a%D != 0 {
		return
	}
	w.Exact = true
	w.Quot = a / D
}

// ProductOK reports the equality D*(a/D) = a on an exact pair, and reports
// false when the pair is not an exact multiple.
func (w *Workspace) ProductOK() bool {
	if !w.Exact {
		return false
	}
	return w.D*w.Quot == w.A
}

// AbsProductOK reports |D|*|a/D| = |a| on an exact pair, and reports false
// when the pair is not an exact multiple. The factors are absolute values, so
// a negative divisor is not collapsed to a signed product.
func (w *Workspace) AbsProductOK() bool {
	if !w.Exact {
		return false
	}
	return absInt(w.D)*absInt(w.Quot) == absInt(w.A)
}

// ProductExact is the signed product predicate. It is false for a zero
// divisor and for a nonzero remainder.
func ProductExact(D, a int64) bool {
	var w Workspace
	w.Load(D, a)
	return w.ProductOK()
}

// AbsProductExact is the absolute product predicate. It is false for a zero
// divisor and for a nonzero remainder.
func AbsProductExact(D, a int64) bool {
	var w Workspace
	w.Load(D, a)
	return w.AbsProductOK()
}

// Cache holds the signed divisor list and the state list for one sweep.
// Both slices are allocated once.
type Cache struct {
	Divisors []int64
	States   []int64
}

// NewCache fills the nonzero divisors and the states of the stated grid.
func NewCache() *Cache {
	divisors := make([]int64, 0, 2*productAbsD)
	for D := int64(-productAbsD); D <= int64(productAbsD); D++ {
		if D != 0 {
			divisors = append(divisors, D)
		}
	}
	states := make([]int64, 0, 2*productAbsA+1)
	for a := int64(-productAbsA); a <= int64(productAbsA); a++ {
		states = append(states, a)
	}
	return &Cache{Divisors: divisors, States: states}
}

// sweepRange checks every pair from the two slices. An exact pair contributes
// the product equality and the absolute-value equality. Any other pair
// contributes two rejections. The quotient of a rejection stays zero.
func sweepRange(divs, states []int64) Totals {
	divs = divs[:len(divs)]
	states = states[:len(states)]
	var t Totals
	var w Workspace
	for i := 0; i < len(states); i++ {
		a := states[i]
		for j := 0; j < len(divs); j++ {
			w.Load(divs[j], a)
			if w.Exact {
				t.check(w.ProductOK())
				t.check(w.AbsProductOK())
			} else {
				t.check(w.Quot == 0)
				t.check(!w.ProductOK())
				t.check(!w.AbsProductOK())
			}
		}
	}
	return t
}

// sweepProduct splits the state list across workers and sums their totals.
func sweepProduct(cache *Cache) Totals {
	states := cache.States
	n := len(states)
	width := (n + productWorkers - 1) / productWorkers
	parts := make([]Totals, productWorkers)
	var wg sync.WaitGroup
	for i := 0; i < productWorkers; i++ {
		begin := i * width
		if begin >= n {
			continue
		}
		end := begin + width
		if end > n {
			end = n
		}
		wg.Add(1)
		go func(idx, begin, end int) {
			defer wg.Done()
			parts[idx] = sweepRange(cache.Divisors, states[begin:end])
		}(i, begin, end)
	}
	wg.Wait()
	var total Totals
	for i := 0; i < len(parts); i++ {
		total.add(parts[i])
	}
	return total
}

// main prints the number of comparisons and exits nonzero on a disagreement.
func main() {
	total := sweepProduct(NewCache())
	fmt.Printf("product checks: %d, failures: %d\n", total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
