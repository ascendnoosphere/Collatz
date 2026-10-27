// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnObstruction checks one affine class on a finite ray.
// The parameters are q=2, c=4, d=4, seed 1, and first hit at time 2.
// Exact int64 arithmetic is used for t from 0 through 500. Agreement on this
// ray is not a proof for every integer in the class.
package main

import (
	"fmt"
	"os"
	"sync"
)

const (
	witnessQ  int64 = 2
	witnessC  int64 = 4
	witnessD  int64 = 4
	witnessN0 int64 = 1
	witnessJ        = 2
	tMax      int64 = 500
	boundA    int64 = 3
	boundB    int64 = 1000
	largeT    int64 = 250
	workers         = 4
)

// Totals counts comparisons, disagreements, and bound outcomes.
type Totals struct {
	Checks   uint64
	Failures uint64
	Holds    uint64
	Breaks   uint64
}

// Workspace holds q^i and T_i(q) through time 2.
type Workspace struct {
	Pow  [3]int64
	Trap [3]int64
}

// Cache stores one multiplier and the powers and offset sums it determines.
type Cache struct {
	Q    int64
	Live bool
	W    Workspace
}

// Prepare fills powers and offset sums for the multiplier q through time 2.
func (w *Workspace) Prepare(q int64) {
	w.Pow[0] = 1
	w.Trap[0] = 0
	var i int
	for i = 0; i < 2; i++ {
		w.Pow[i+1] = w.Pow[i] * q
		w.Trap[i+1] = w.Trap[i] + w.Pow[i]
	}
}

// NewCache allocates an unloaded cache.
func NewCache() *Cache {
	return &Cache{}
}

// Load records q and prepares its power table.
func (c *Cache) Load(q int64) {
	c.W.Prepare(q)
	c.Q = q
	c.Live = true
}

// AbsInt returns the absolute value of v. The caller keeps v away from the
// most negative int64.
func AbsInt(v int64) int64 {
	if v < 0 {
		return -v
	}
	return v
}

// Divides reports whether d divides a. A zero divisor divides nothing here.
func Divides(d, a int64) bool {
	if d == 0 {
		return false
	}
	return a%d == 0
}

// AffineAt returns pow*n + c*trap, the affine state at one prepared time.
func AffineAt(pow, trap, c, n int64) int64 {
	return pow*n + c*trap
}

// IsFirstHit reports that time j is the first time d divides the affine state.
func IsFirstHit(pow, trap []int64, c, d, n int64, j int) bool {
	if j < 0 || j >= len(pow) || j >= len(trap) {
		return false
	}
	pow = pow[:j+1]
	trap = trap[:j+1]
	if !Divides(d, AffineAt(pow[j], trap[j], c, n)) {
		return false
	}
	var i int
	for i = 0; i < j; i++ {
		if Divides(d, AffineAt(pow[i], trap[i], c, n)) {
			return false
		}
	}
	return true
}

// SameClass reports that d divides n-n0. A zero divisor is rejected.
func SameClass(n, n0, d int64) bool {
	if d == 0 {
		return false
	}
	return (n-n0)%d == 0
}

// QuotientProductMatches reports |d|*|q| = |aff|.
func QuotientProductMatches(d, q, aff int64) bool {
	return AbsInt(d)*AbsInt(q) == AbsInt(aff)
}

// ClassBoundHolds reports |d|*|h| <= a*|n| + b for the supplied nonnegative data.
func ClassBoundHolds(dAbs, hAbs, a, nAbs, b int64) bool {
	return dAbs*hAbs <= a*nAbs+b
}

// QuotientAbs returns the absolute value of the exact affine quotient by d.
func QuotientAbs(pow, trap, c, n, d int64) int64 {
	return AbsInt(AffineAt(pow, trap, c, n) / d)
}

// AddTotals sums worker totals. Addition of these counters is commutative.
func AddTotals(parts []Totals) Totals {
	var total Totals
	parts = parts[:len(parts)]
	var i int
	for i = 0; i < len(parts); i++ {
		total.Checks += parts[i].Checks
		total.Failures += parts[i].Failures
		total.Holds += parts[i].Holds
		total.Breaks += parts[i].Breaks
	}
	return total
}

// CheckSeed records the first hit and the absolute-value product at time 2.
func CheckSeed(pow, trap []int64, n, d int64, total *Totals) {
	total.Checks++
	if !IsFirstHit(pow, trap, witnessC, d, n, witnessJ) {
		total.Failures++
	}
	aff := AffineAt(pow[witnessJ], trap[witnessJ], witnessC, n)
	total.Checks++
	if !QuotientProductMatches(d, aff/d, aff) {
		total.Failures++
	}
}

// SweepRange checks the ray n0+t*|d| for t from lo through hi.
func SweepRange(lo, hi int64, c *Cache, total *Totals) {
	pow := c.W.Pow[:len(c.W.Pow)]
	trap := c.W.Trap[:len(c.W.Trap)]
	var t int64
	for t = lo; t <= hi; t++ {
		n := witnessN0 + t*witnessD
		CheckSeed(pow, trap, n, witnessD, total)
		CheckSeed(pow, trap, n, -witnessD, total)
		total.Checks++
		if !SameClass(n, witnessN0, witnessD) {
			total.Failures++
		}
		h := QuotientAbs(pow[witnessJ], trap[witnessJ], witnessC, n, witnessD)
		total.Checks++
		if ClassBoundHolds(witnessD, h, boundA, AbsInt(n), boundB) {
			total.Holds++
		} else {
			total.Breaks++
		}
	}
}

// RunClassSweep checks t from 0 through 500 on four contiguous chunks.
func RunClassSweep() Totals {
	count := tMax + 1
	width := (count + workers - 1) / workers
	var chunks [workers]Totals
	var wg sync.WaitGroup
	var i int64
	for i = 0; i < workers; i++ {
		lo := i * width
		hi := lo + width - 1
		if lo > tMax {
			continue
		}
		if hi > tMax {
			hi = tMax
		}
		wg.Add(1)
		go func(idx int, lo, hi int64) {
			defer wg.Done()
			cache := NewCache()
			cache.Load(witnessQ)
			SweepRange(lo, hi, cache, &chunks[idx])
		}(int(i), lo, hi)
	}
	wg.Wait()
	return AddTotals(chunks[:])
}

// LargeWitness reports the seed 1+250*4 and whether 4*|H| exceeds 3*|n|+1000.
func LargeWitness(c *Cache) (n, h, left, right int64, breaks bool) {
	pow := c.W.Pow[witnessJ]
	trap := c.W.Trap[witnessJ]
	n = witnessN0 + largeT*witnessD
	h = QuotientAbs(pow, trap, witnessC, n, witnessD)
	left = witnessD * h
	right = boundA*AbsInt(n) + boundB
	breaks = left > right
	return n, h, left, right, breaks
}

// main prints the ray counts and the seed 1001, and exits nonzero on failure.
func main() {
	cache := NewCache()
	cache.Load(witnessQ)
	total := RunClassSweep()
	n, h, left, right, breaks := LargeWitness(cache)
	fmt.Printf("checks %d\n", total.Checks)
	fmt.Printf("failures %d\n", total.Failures)
	fmt.Printf("holds %d\n", total.Holds)
	fmt.Printf("breaks %d\n", total.Breaks)
	fmt.Printf("witness n=%d absH=%d left=%d right=%d breaks=%t\n",
		n, h, left, right, breaks)
	fmt.Printf("finite ray only; not a proof for every integer\n")
	if total.Failures != 0 || !breaks || total.Breaks == 0 {
		os.Exit(1)
	}
}
