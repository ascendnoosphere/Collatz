// SPDX-License-Identifier: CC-BY-4.0
// Equal odd components of a two-affine word, checked on a finite integer grid.
package main

import (
	"fmt"
	"os"
	"sync"
)

const (
	maxHalf  = 12
	maxOddQ  = 4095
	probeN   = 8
	maxM     = 12
	maxLet   = 6
	maxState = 16
	maxMult  = 32
	chunks   = 4
)

// Cache holds powers of two through the half-exponent bound.
type Cache struct {
	Pow []uint64
}

// Workspace holds the two sides of one integer comparison.
type Workspace struct {
	Left  uint64
	Right uint64
}

// NewCache returns 2^0 through 2^maxHalf.
func NewCache() *Cache {
	pow := make([]uint64, maxHalf+1)
	pow[0] = 1
	for i := 1; i <= maxHalf; i++ {
		pow[i] = pow[i-1] << 1
	}
	return &Cache{Pow: pow}
}

// ClosureHolds reports whether q*n+1 equals pow*n, for products that fit in uint64.
func ClosureHolds(ws *Workspace, q, n, pow uint64) bool {
	if n == 0 {
		return false
	}
	if q != 0 && n > ^uint64(0)/q {
		return false
	}
	if pow != 0 && n > ^uint64(0)/pow {
		return false
	}
	ws.Left = q*n + 1
	ws.Right = pow * n
	return ws.Left == ws.Right
}

// IsUnitEqual reports the positive solution n=1, q+1=2^a.
func IsUnitEqual(q, a, n uint64) bool {
	if a == 0 || a >= 63 || n != 1 {
		return false
	}
	return q+1 == uint64(1)<<a
}

// AlwaysTrue accepts every triple. It is not the equal-component test.
func AlwaysTrue(q, a, n uint64) bool {
	return true
}

// UnequalComponentsExcluded reports whether unequal components were excluded.
// This grid does not decide that question.
func UnequalComponentsExcluded() bool {
	return false
}

// ExpectedChecks is the number of integer comparisons in Run.
// It is 12*2048*8 + (2^12-1) + 30*16*16 = 208383.
func ExpectedChecks() uint64 {
	odds := uint64((maxOddQ + 1) / 2)
	perQ := uint64(2 + (probeN - 2))
	half := uint64(maxHalf) * odds * perQ
	factors := (uint64(1) << maxM) - 1
	pairs := uint64(maxLet * (maxLet - 1))
	states := uint64(maxState)
	mults := uint64(maxMult / 2)
	return half + factors + pairs*states*mults
}

// sweepHalf checks one half exponent against every odd multiplier in range.
func sweepHalf(ws *Workspace, cache *Cache, t uint64) (uint64, uint64) {
	var checks, failures uint64
	pow := cache.Pow[t]
	for q := uint64(1); q <= maxOddQ; q += 2 {
		unit := q+1 == pow
		checks++
		if ClosureHolds(ws, q, 1, pow) != unit {
			failures++
		}
		checks++
		if pow > q {
			if (pow-q == 1) != unit {
				failures++
			}
		} else if unit {
			failures++
		}
		for n := uint64(3); n <= probeN; n++ {
			checks++
			if ClosureHolds(ws, q, n, pow) {
				failures++
			}
		}
	}
	return checks, failures
}

// sweepRange checks a contiguous interval of half exponents.
func sweepRange(cache *Cache, lo, hi uint64) (uint64, uint64) {
	ws := Workspace{}
	var checks, failures uint64
	for t := lo; t <= hi; t++ {
		c, f := sweepHalf(&ws, cache, t)
		checks += c
		failures += f
	}
	return checks, failures
}

// factorChecks verifies 2^{2m}-q^2 = (2^m-q)(2^m+q) for odd q below 2^m.
func factorChecks(cache *Cache) (uint64, uint64) {
	ws := Workspace{}
	var checks, failures uint64
	for m := uint64(1); m <= maxM; m++ {
		pow := cache.Pow[m]
		for q := uint64(1); q < pow; q += 2 {
			checks++
			ws.Left = (pow - q) * (pow + q)
			ws.Right = pow*pow - q*q
			if ws.Left != ws.Right {
				failures++
			}
		}
	}
	return checks, failures
}

// letterChecks rejects equal components at two different positive letters.
func letterChecks(cache *Cache) (uint64, uint64) {
	ws := Workspace{}
	var checks, failures uint64
	for a := uint64(1); a <= maxLet; a++ {
		for b := uint64(1); b <= maxLet; b++ {
			if a == b {
				continue
			}
			pa := cache.Pow[a]
			pb := cache.Pow[b]
			for n := uint64(1); n <= maxState; n++ {
				for q := uint64(1); q <= maxMult; q += 2 {
					checks++
					left := ClosureHolds(&ws, q, n, pa)
					right := ClosureHolds(&ws, q, n, pb)
					if left && right {
						failures++
					}
				}
			}
		}
	}
	return checks, failures
}

// Run counts the equal-component checks. A zero failure count is not the theorem.
func Run(cache *Cache) (uint64, uint64) {
	var wg sync.WaitGroup
	cs := make([]uint64, chunks)
	fs := make([]uint64, chunks)
	span := uint64(maxHalf / chunks)
	for i := 0; i < chunks; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			lo := uint64(i)*span + 1
			hi := lo + span - 1
			cs[i], fs[i] = sweepRange(cache, lo, hi)
		}(i)
	}
	wg.Wait()
	var checks, failures uint64
	for i := 0; i < chunks; i++ {
		checks += cs[i]
		failures += fs[i]
	}
	c, f := factorChecks(cache)
	checks += c
	failures += f
	c, f = letterChecks(cache)
	checks += c
	failures += f
	return checks, failures
}

// main prints the number of equal-component integer checks on the stated grid.
func main() {
	cache := NewCache()
	checks, failures := Run(cache)
	fmt.Printf("equal odd component checks: %d\n", checks)
	fmt.Printf("failures: %d\n", failures)
	if failures != 0 {
		os.Exit(1)
	}
}
