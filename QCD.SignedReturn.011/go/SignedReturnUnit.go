// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnUnit checks the multiplier-one return on a finite grid.
// The affine state is compared with n+j*c, and each first hit is compared with
// the quotient (n+j*c)/d and with the bound |d|*|return| <= |n|+j*|c|.
// Arithmetic is exact int64 on the stated bounds. Agreement on this grid is
// not a proof for every integer.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the exact grid. The multiplier is 1. Offsets satisfy |c| <= 6,
// seeds lie in -20..20, and times run through 0..8. Admissible divisors are
// ±2, ±3, and ±5. Then |n+j*c| <= 20+48 = 68, and |d| times a return is at
// most 5*68 = 340. Every product used below fits in an int64.
const (
	unitCMin    = -6
	unitCMax    = 6
	unitNMin    = -20
	unitNMax    = 20
	unitJMax    = 8
	unitWorkers = 4
)

// Totals counts comparisons, disagreements, and first hits of one sweep.
type Totals struct {
	Checks   uint64
	Failures uint64
	Hits     uint64
}

// Workspace holds q^j and the offset sum for one multiplier and time.
// It is reused by a single worker and is not safe for concurrent calls.
type Workspace struct {
	Pow  int64
	Trap int64
}

// NewWorkspace returns an empty power-and-sum workspace.
func NewWorkspace() *Workspace {
	return &Workspace{}
}

// Prepare stores q^j and the sum of q^0 through q^(j-1). The empty sum is
// zero and the empty power is one.
func (w *Workspace) Prepare(q int64, j int) {
	pow := int64(1)
	trap := int64(0)
	for i := 0; i < j; i++ {
		trap += pow
		pow *= q
	}
	w.Pow = pow
	w.Trap = trap
}

// Cache holds q^i and the offset sum through the unit horizon.
// Load refills the existing buffers. A cache is not safe for concurrent calls.
type Cache struct {
	Q    int64
	Pow  []int64
	Trap []int64
	Live bool
}

// NewCache allocates the unit power and offset buffers once.
func NewCache() *Cache {
	return &Cache{
		Pow:  make([]int64, unitJMax+1),
		Trap: make([]int64, unitJMax+1),
	}
}

// Load fills every time from zero through the unit horizon for multiplier q.
func (c *Cache) Load(q int64) {
	pow := int64(1)
	trap := int64(0)
	ps := c.Pow[:len(c.Pow)]
	ts := c.Trap[:len(c.Trap)]
	for j := 0; j < len(ps); j++ {
		ps[j] = pow
		ts[j] = trap
		trap += pow
		pow *= q
	}
	c.Q = q
	c.Live = true
}

// AbsInt returns the absolute value of an int64 away from the sign bit.
// The grid never reaches the minimum int64, where negation would overflow.
func AbsInt(k int64) int64 {
	if k < 0 {
		return -k
	}
	return k
}

// Divides reports whether d divides a in Z. Zero divides only zero.
func Divides(d, a int64) bool {
	if d == 0 {
		return a == 0
	}
	return a%d == 0
}

// RawStep is the signed raw map: exact division on a multiple, otherwise q*n+c.
func RawStep(q, c, d, n int64) int64 {
	if Divides(d, n) {
		return n / d
	}
	return q*n + c
}

// IterateRaw applies RawStep exactly j times, starting at n.
func IterateRaw(q, c, d, n int64, j int) int64 {
	s := n
	for i := 0; i < j; i++ {
		s = RawStep(q, c, d, s)
	}
	return s
}

// AffineIs reports whether the multiplier-one affine state equals claimed.
// The state is q^j*n+c*T_j(q) with q fixed at 1, not the closed form n+j*c.
func AffineIs(w *Workspace, c, n int64, j int, claimed int64) bool {
	w.Prepare(1, j)
	return w.Pow*n+c*w.Trap == claimed
}

// IsFirstHit reports whether j is the first time d divides the affine state.
// The cache must already be loaded for its multiplier, through at least time j.
func IsFirstHit(c *Cache, coeff, d, n int64, j int) bool {
	ps := c.Pow[:len(c.Pow)]
	ts := c.Trap[:len(c.Trap)]
	if !c.Live || j < 0 || j >= len(ps) {
		return false
	}
	if !Divides(d, ps[j]*n+coeff*ts[j]) {
		return false
	}
	for i := 0; i < j; i++ {
		if Divides(d, ps[i]*n+coeff*ts[i]) {
			return false
		}
	}
	return true
}

// ReturnIs reports whether j is a first hit and the next raw step equals claimed.
// A non-hit returns false, so a constant true predicate does not satisfy it.
func ReturnIs(cache *Cache, c, d, n int64, j int, claimed int64) bool {
	if !IsFirstHit(cache, c, d, n, j) {
		return false
	}
	state := IterateRaw(cache.Q, c, d, n, j)
	return RawStep(cache.Q, c, d, state) == claimed
}

// MagnitudeIs reports whether j is a first hit and |d|*|return| is at most bound.
// A non-hit returns false. The return is the next raw step, not a supplied quotient.
func MagnitudeIs(cache *Cache, c, d, n int64, j int, bound int64) bool {
	if !IsFirstHit(cache, c, d, n, j) {
		return false
	}
	state := IterateRaw(cache.Q, c, d, n, j)
	ret := RawStep(cache.Q, c, d, state)
	return AbsInt(d)*AbsInt(ret) <= bound
}

// CoreAtSeed reports the core comparison at one first hit.
// It requires |q| < |d| and |d|*|return| <= |q|*|n| + offset, with offset = j*|c|
// in the unit sweep. A non-hit, or a multiplier that does not match the cache,
// returns false.
func CoreAtSeed(cache *Cache, q, c, d, n int64, j int, offset int64) bool {
	if !cache.Live || cache.Q != q || !IsFirstHit(cache, c, d, n, j) {
		return false
	}
	aq := AbsInt(q)
	ad := AbsInt(d)
	if aq >= ad {
		return false
	}
	state := IterateRaw(q, c, d, n, j)
	ret := RawStep(q, c, d, state)
	return ad*AbsInt(ret) <= aq*AbsInt(n)+offset
}

// unitDivisors returns the admissible divisors of the unit sweep.
func unitDivisors() [6]int64 {
	return [6]int64{-5, -3, -2, 2, 3, 5}
}

// sweepSeed checks the unit identities for one seed on the full offset-time grid.
// The cache must already be loaded at multiplier 1. A different load is a failure
// and contributes no grid comparisons.
func sweepSeed(n int64, w *Workspace, cache *Cache, total *Totals) {
	if !cache.Live || cache.Q != 1 {
		total.Failures++
		return
	}
	for c := int64(unitCMin); c <= unitCMax; c++ {
		for j := 0; j <= unitJMax; j++ {
			claimed := n + int64(j)*c
			total.Checks++
			if !AffineIs(w, c, n, j, claimed) {
				total.Failures++
			}
		}
	}
	divs := unitDivisors()
	ds := divs[:]
	for di := 0; di < len(ds); di++ {
		d := ds[di]
		for c := int64(unitCMin); c <= unitCMax; c++ {
			for j := 0; j <= unitJMax; j++ {
				total.Checks++
				if !IsFirstHit(cache, c, d, n, j) {
					continue
				}
				total.Hits++
				numer := n + int64(j)*c
				if IterateRaw(1, c, d, n, j) != numer {
					total.Failures++
				}
				if numer/d*d != numer {
					total.Failures++
				}
				if !ReturnIs(cache, c, d, n, j, numer/d) {
					total.Failures++
				}
				bound := AbsInt(n) + int64(j)*AbsInt(c)
				if !MagnitudeIs(cache, c, d, n, j, bound) {
					total.Failures++
				}
				if !CoreAtSeed(cache, 1, c, d, n, j, int64(j)*AbsInt(c)) {
					total.Failures++
				}
			}
		}
	}
}

// DomainSize counts affine comparisons plus first-hit slots, without evaluating them.
func DomainSize() uint64 {
	cCount := uint64(unitCMax - unitCMin + 1)
	nCount := uint64(unitNMax - unitNMin + 1)
	jCount := uint64(unitJMax + 1)
	affine := cCount * nCount * jCount
	return affine + affine*6
}

// runSeeds splits the closed seed interval across workers.
// Each worker owns one workspace, one cache loaded at multiplier 1, and one totals slot.
func runSeeds(fn func(int64, *Workspace, *Cache, *Totals)) Totals {
	loAll := int64(unitNMin)
	hiAll := int64(unitNMax)
	count := int(hiAll - loAll + 1)
	width := (count + unitWorkers - 1) / unitWorkers
	chunks := make([]Totals, unitWorkers)
	var wg sync.WaitGroup
	for i := 0; i < unitWorkers; i++ {
		lo := loAll + int64(i*width)
		hi := lo + int64(width) - 1
		if lo > hiAll {
			continue
		}
		if hi > hiAll {
			hi = hiAll
		}
		wg.Add(1)
		go func(idx int, lo, hi int64) {
			defer wg.Done()
			w := NewWorkspace()
			cache := NewCache()
			cache.Load(1)
			for n := lo; n <= hi; n++ {
				fn(n, w, cache, &chunks[idx])
			}
		}(i, lo, hi)
	}
	wg.Wait()
	var total Totals
	part := chunks[:len(chunks)]
	for i := 0; i < len(part); i++ {
		total.Checks += part[i].Checks
		total.Failures += part[i].Failures
		total.Hits += part[i].Hits
	}
	return total
}

// RunUnitSweep checks the unit affine form, return, and magnitude on every grid tuple.
func RunUnitSweep() Totals {
	return runSeeds(sweepSeed)
}

// main prints the number of exact comparisons and exits nonzero on a disagreement.
func main() {
	got := RunUnitSweep()
	fmt.Printf("unit return checks: %d, failures: %d\n", got.Checks, got.Failures)
	if got.Failures != 0 {
		os.Exit(1)
	}
}
