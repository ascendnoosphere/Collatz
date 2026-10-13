// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnShift checks the affine-state shift on a finite grid.
// Replacing n by n+t*d adds q^j*t*d to the affine state. The arithmetic is
// exact int64 on the stated bounds. Agreement on this grid is not a proof of
// the identity for every integer.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the exact grid. With |q| <= 3 and j <= 6 one has |q|^j <= 729.
// The identity sweep uses |n| <= 5, |c| <= 4, |t| <= 5 and |d| <= 5, so
// |n+t*d| <= 30 and |q^j*(n+t*d)| <= 21870. The offset sum has absolute value
// at most (3^6-1)/2 = 364, and |c| times that sum is at most 1456. The first-hit
// sweep uses |q| <= 3, j <= 4, |c| <= 2, |n| <= 6, |t| <= 3 and the six
// divisors ±2, ±3, ±5. Every product used below fits in an int64.
const (
	shiftQMin    = -3
	shiftQMax    = 3
	shiftJMax    = 6
	shiftNMin    = -5
	shiftNMax    = 5
	shiftCMin    = -4
	shiftCMax    = 4
	shiftTMin    = -5
	shiftTMax    = 5
	shiftDMin    = -5
	shiftDMax    = 5
	hitQMin      = -3
	hitQMax      = 3
	hitJMax      = 4
	hitNMin      = -6
	hitNMax      = 6
	hitCMin      = -2
	hitCMax      = 2
	hitTMin      = -3
	hitTMax      = 3
	shiftWorkers = 4
)

// Totals counts comparisons, disagreements, and first hits of one sweep.
type Totals struct {
	Checks   uint64
	Failures uint64
	Hits     uint64
}

// Workspace holds the power q^j and the offset sum for one multiplier and time.
// It is reused by a single worker and is not safe for concurrent calls.
type Workspace struct {
	Pow  int64
	Trap int64
}

// NewWorkspace returns an empty power-and-sum workspace.
func NewWorkspace() *Workspace {
	return &Workspace{}
}

// Prepare stores q^j and the sum of q^0 through q^(j-1). The empty sum is zero,
// and the empty power is one, including the case q = 0 and j = 0.
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

// Cache holds q^i and the offset sum at every time up to the first-hit horizon.
// Load refills the existing buffers. A cache is not safe for concurrent calls.
type Cache struct {
	Q    int64
	Pow  []int64
	Trap []int64
	Live bool
}

// NewCache allocates the first-hit power and offset buffers once.
func NewCache() *Cache {
	return &Cache{
		Pow:  make([]int64, hitJMax+1),
		Trap: make([]int64, hitJMax+1),
	}
}

// Load fills every time from zero through the first-hit horizon for multiplier q.
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

// AffineValue returns q^j*n + c*T_j(q) from a prepared power and offset sum.
func AffineValue(pow, trap, c, n int64) int64 {
	return pow*n + c*trap
}

// IncrementIs reports whether the affine increment equals the claimed integer.
// The claim q^j*t*d is the proved shift. A different claim is false on this grid.
func IncrementIs(pow, trap, c, n, t, d, claimed int64) bool {
	left := AffineValue(pow, trap, c, n+t*d)
	right := AffineValue(pow, trap, c, n)
	return left-right == claimed
}

// Divides reports whether d divides a in Z. Zero divides only zero.
func Divides(d, a int64) bool {
	if d == 0 {
		return a == 0
	}
	return a%d == 0
}

// IsFirstHit reports whether j is the first time d divides the affine state.
// The cache must already be loaded for the multiplier, through at least time j.
func IsFirstHit(c *Cache, coeff, d, n int64, j int) bool {
	ps := c.Pow[:len(c.Pow)]
	ts := c.Trap[:len(c.Trap)]
	if !c.Live || j < 0 || j >= len(ps) {
		return false
	}
	if !Divides(d, AffineValue(ps[j], ts[j], coeff, n)) {
		return false
	}
	for i := 0; i < j; i++ {
		if Divides(d, AffineValue(ps[i], ts[i], coeff, n)) {
			return false
		}
	}
	return true
}

// hitDivisors returns the admissible divisors used by the first-hit sweep.
func hitDivisors() [6]int64 {
	return [6]int64{-5, -3, -2, 2, 3, 5}
}

// sweepIdentityQ checks the shift identity for one multiplier on the full grid.
func sweepIdentityQ(q int64, w *Workspace, total *Totals) {
	for j := 0; j <= shiftJMax; j++ {
		w.Prepare(q, j)
		for c := int64(shiftCMin); c <= shiftCMax; c++ {
			for n := int64(shiftNMin); n <= shiftNMax; n++ {
				for t := int64(shiftTMin); t <= shiftTMax; t++ {
					for d := int64(shiftDMin); d <= shiftDMax; d++ {
						claimed := w.Pow * t * d
						total.Checks++
						if !IncrementIs(w.Pow, w.Trap, c, n, t, d, claimed) {
							total.Failures++
						}
					}
				}
			}
		}
	}
}

// sweepHitQ checks first-hit transport for one multiplier. Each admissible
// divisor, seed, shift, offset, and time contributes one comparison. A hit is
// counted once, on the unshifted seed.
func sweepHitQ(q int64, cache *Cache, total *Totals) {
	cache.Load(q)
	divs := hitDivisors()
	divsSl := divs[:]
	for di := 0; di < len(divsSl); di++ {
		d := divsSl[di]
		for c := int64(hitCMin); c <= hitCMax; c++ {
			for n := int64(hitNMin); n <= hitNMax; n++ {
				for t := int64(hitTMin); t <= hitTMax; t++ {
					for j := 0; j <= hitJMax; j++ {
						left := IsFirstHit(cache, c, d, n, j)
						right := IsFirstHit(cache, c, d, n+t*d, j)
						total.Checks++
						if left != right {
							total.Failures++
						}
						if left {
							total.Hits++
						}
					}
				}
			}
		}
	}
}

// IdentityDomainSize counts the identity tuples without evaluating the shift.
func IdentityDomainSize() uint64 {
	var count uint64
	for q := int64(shiftQMin); q <= shiftQMax; q++ {
		for j := 0; j <= shiftJMax; j++ {
			for c := int64(shiftCMin); c <= shiftCMax; c++ {
				for n := int64(shiftNMin); n <= shiftNMax; n++ {
					for t := int64(shiftTMin); t <= shiftTMax; t++ {
						for d := int64(shiftDMin); d <= shiftDMax; d++ {
							count++
						}
					}
				}
			}
		}
	}
	return count
}

// HitDomainSize counts the first-hit tuples without evaluating the predicate.
func HitDomainSize() uint64 {
	var count uint64
	divs := hitDivisors()
	for q := int64(hitQMin); q <= hitQMax; q++ {
		for di := 0; di < len(divs); di++ {
			for c := int64(hitCMin); c <= hitCMax; c++ {
				for n := int64(hitNMin); n <= hitNMax; n++ {
					for t := int64(hitTMin); t <= hitTMax; t++ {
						for j := 0; j <= hitJMax; j++ {
							count++
						}
					}
				}
			}
		}
	}
	return count
}

// runChunked splits the closed multiplier interval across workers. Each worker
// owns one workspace, one cache, and one totals slot.
func runChunked(loAll, hiAll int64, fn func(int64, *Workspace, *Cache, *Totals)) Totals {
	count := int(hiAll - loAll + 1)
	width := (count + shiftWorkers - 1) / shiftWorkers
	chunks := make([]Totals, shiftWorkers)
	var wg sync.WaitGroup
	for i := 0; i < shiftWorkers; i++ {
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
			for q := lo; q <= hi; q++ {
				fn(q, w, cache, &chunks[idx])
			}
		}(i, lo, hi)
	}
	wg.Wait()
	var total Totals
	for i := 0; i < len(chunks); i++ {
		total.Checks += chunks[i].Checks
		total.Failures += chunks[i].Failures
		total.Hits += chunks[i].Hits
	}
	return total
}

// RunIdentitySweep checks the difference identity on every identity-grid tuple.
func RunIdentitySweep() Totals {
	return runChunked(shiftQMin, shiftQMax, func(q int64, w *Workspace, _ *Cache, total *Totals) {
		sweepIdentityQ(q, w, total)
	})
}

// RunHitSweep checks first-hit transport on every first-hit-grid tuple.
func RunHitSweep() Totals {
	return runChunked(hitQMin, hitQMax, func(q int64, _ *Workspace, cache *Cache, total *Totals) {
		sweepHitQ(q, cache, total)
	})
}

// main prints the number of exact comparisons and exits nonzero on a disagreement.
func main() {
	identity := RunIdentitySweep()
	hits := RunHitSweep()
	checks := identity.Checks + hits.Checks
	failures := identity.Failures + hits.Failures
	fmt.Printf("affine shift checks: %d, failures: %d\n", checks, failures)
	if failures != 0 {
		os.Exit(1)
	}
}
