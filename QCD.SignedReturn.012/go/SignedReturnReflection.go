// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnReflection checks the multiplier -1 on a finite grid.
// Even times equal the seed and odd times equal c-n. Each seed falls into
// one of three clauses: divisor meets n, divisor meets c-n but not n, or
// neither. Exact int64 arithmetic is used inside the stated bounds.
// Agreement on this grid is not a proof for every integer.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the exact grid. The multiplier is -1, so every power is ±1 and
// every offset sum is 0 or 1. With |c| ≤ 4 and |n| ≤ 6 the affine state has
// absolute value at most 10. Divisors are the eight integers ±2, ±3, ±4, ±5,
// and times run from 0 through 6. Every product used below fits in an int64.
const (
	refCMin       = -4
	refCMax       = 4
	refNMin       = -6
	refNMax       = 6
	refJMax       = 6
	refWorkers    = 4
	checksPerSeed = 20
)

// Clause records which of the three divisibility alternatives occurred.
const (
	clauseHitZero = 0
	clauseHitOne  = 1
	clauseTrap    = 2
)

// Census counts comparisons, disagreements, and the three clauses.
type Census struct {
	Checks   uint64
	Failures uint64
	HitZero  uint64
	HitOne   uint64
	Trap     uint64
}

// Workspace holds one power of -1 and the matching offset sum.
// A workspace is reused by a single caller and is not safe for concurrent use.
type Workspace struct {
	Pow  int64
	Trap int64
}

// NewWorkspace returns an empty power-and-sum workspace.
func NewWorkspace() *Workspace {
	return &Workspace{}
}

// Prepare stores (-1)^j and the sum of (-1)^0 through (-1)^(j-1).
// The empty power is 1 and the empty sum is 0.
func (w *Workspace) Prepare(j int) {
	pow := int64(1)
	trap := int64(0)
	for i := 0; i < j; i++ {
		trap += pow
		pow *= -1
	}
	w.Pow = pow
	w.Trap = trap
}

// Cache holds (-1)^j and the offset sum at every time through refJMax.
// Load refills the existing buffers. A cache is not safe for concurrent calls.
type Cache struct {
	Pow  []int64
	Trap []int64
}

// NewCache allocates the power and offset buffers once and fills them.
func NewCache() *Cache {
	c := &Cache{
		Pow:  make([]int64, refJMax+1),
		Trap: make([]int64, refJMax+1),
	}
	c.Load()
	return c
}

// Load fills every time from zero through refJMax for the multiplier -1.
func (c *Cache) Load() {
	pow := int64(1)
	trap := int64(0)
	ps := c.Pow[:len(c.Pow)]
	ts := c.Trap[:len(c.Trap)]
	for j := 0; j < len(ps); j++ {
		ps[j] = pow
		ts[j] = trap
		trap += pow
		pow *= -1
	}
}

// ClosedForm is the seed at an even time and c-n at an odd time.
func ClosedForm(j int, c, n int64) int64 {
	if j%2 == 0 {
		return n
	}
	return c - n
}

// StateEquals reports whether (-1)^j*n + c*T_j(-1) equals the claimed integer.
// A claim other than the affine state is false. Replacing this by true accepts
// that false claim.
func StateEquals(pow, trap, c, n, claimed int64) bool {
	return pow*n+c*trap == claimed
}

// Divides reports whether d divides a in Z. Zero divides only zero.
func Divides(d, a int64) bool {
	if d == 0 {
		return a == 0
	}
	return a%d == 0
}

// admissibleDivisors returns the eight divisors with absolute value 2 through 5.
func admissibleDivisors() [8]int64 {
	return [8]int64{-5, -4, -3, -2, 2, 3, 4, 5}
}

// ClauseOf reports which alternative holds for divisor d, offset c, and seed n.
// Clause 0: d divides n. Clause 1: d misses n but divides c-n. Clause 2: neither.
func ClauseOf(d, c, n int64) int {
	if Divides(d, n) {
		return clauseHitZero
	}
	if Divides(d, c-n) {
		return clauseHitOne
	}
	return clauseTrap
}

// IsFirstHit reports whether j is the first time d divides the affine state.
// The slices must contain times 0 through j. A later divisible time is not first.
func IsFirstHit(pow, trap []int64, d, c, n int64, j int) bool {
	pow = pow[:len(pow)]
	trap = trap[:len(trap)]
	if j < 0 || j >= len(pow) {
		return false
	}
	if !Divides(d, pow[j]*n+c*trap[j]) {
		return false
	}
	for i := 0; i < j; i++ {
		if Divides(d, pow[i]*n+c*trap[i]) {
			return false
		}
	}
	return true
}

// checkSeed compares one seed with the closed form, the two-step repetition,
// and the clause predicted by divisibility of n and of c-n.
func checkSeed(pow, trap []int64, d, c, n int64, cen *Census) {
	pow = pow[:len(pow)]
	trap = trap[:len(trap)]
	kind := ClauseOf(d, c, n)
	switch kind {
	case clauseHitZero:
		cen.HitZero++
	case clauseHitOne:
		cen.HitOne++
	default:
		cen.Trap++
	}
	for j := 0; j <= refJMax; j++ {
		wantHit := false
		if kind == clauseHitZero && j == 0 {
			wantHit = true
		}
		if kind == clauseHitOne && j == 1 {
			wantHit = true
		}
		cen.Checks++
		if IsFirstHit(pow, trap, d, c, n, j) != wantHit {
			cen.Failures++
		}
		cen.Checks++
		if !StateEquals(pow[j], trap[j], c, n, ClosedForm(j, c, n)) {
			cen.Failures++
		}
	}
	// Times 0 and 1 are the base steps: compare 2 with 0 and 3 with 1.
	for j := 0; j+2 <= refJMax; j++ {
		left := pow[j+2]*n + c*trap[j+2]
		right := pow[j]*n + c*trap[j]
		cen.Checks++
		if left != right {
			cen.Failures++
		}
	}
	cen.Checks++
	switch kind {
	case clauseHitZero:
		if d*(n/d) != n {
			cen.Failures++
		}
	case clauseHitOne:
		diff := c - n
		if d*(diff/d) != diff {
			cen.Failures++
		}
	default:
		if Divides(d, n) || Divides(d, c-n) {
			cen.Failures++
		}
	}
}

// sweepRange checks every divisor and seed for offsets from cLo through cHi.
func sweepRange(cache *Cache, cLo, cHi int64) Census {
	var cen Census
	divs := admissibleDivisors()
	ds := divs[:]
	ps := cache.Pow[:len(cache.Pow)]
	ts := cache.Trap[:len(cache.Trap)]
	for c := cLo; c <= cHi; c++ {
		for n := int64(refNMin); n <= refNMax; n++ {
			for di := 0; di < len(ds); di++ {
				checkSeed(ps, ts, ds[di], c, n, &cen)
			}
		}
	}
	return cen
}

// DomainSeeds counts offset-seed-divisor triples without evaluating them.
func DomainSeeds() uint64 {
	cs := uint64(refCMax - refCMin + 1)
	ns := uint64(refNMax - refNMin + 1)
	return cs * ns * 8
}

// RunSweep checks the reflection on every grid triple, split across workers.
func RunSweep() Census {
	cLo := int64(refCMin)
	cHi := int64(refCMax)
	count := int(cHi - cLo + 1)
	width := (count + refWorkers - 1) / refWorkers
	parts := make([]Census, refWorkers)
	var wg sync.WaitGroup
	for i := 0; i < refWorkers; i++ {
		lo := cLo + int64(i*width)
		hi := lo + int64(width) - 1
		if lo > cHi {
			continue
		}
		if hi > cHi {
			hi = cHi
		}
		wg.Add(1)
		go func(idx int, lo, hi int64) {
			defer wg.Done()
			cache := NewCache()
			parts[idx] = sweepRange(cache, lo, hi)
		}(i, lo, hi)
	}
	wg.Wait()
	var total Census
	for i := 0; i < len(parts); i++ {
		total.Checks += parts[i].Checks
		total.Failures += parts[i].Failures
		total.HitZero += parts[i].HitZero
		total.HitOne += parts[i].HitOne
		total.Trap += parts[i].Trap
	}
	return total
}

// main prints the check count and the three clause counts.
func main() {
	cen := RunSweep()
	fmt.Printf(
		"reflection checks: %d, failures: %d, clause0: %d, clause1: %d, clause2: %d\n",
		cen.Checks, cen.Failures, cen.HitZero, cen.HitOne, cen.Trap)
	if cen.Failures != 0 {
		os.Exit(1)
	}
}
