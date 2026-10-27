// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnUniform counts first hits of the affine state for
// multiplier 1 and divisors ±2 on a finite seed grid. For this multiplier
// the state at time j is n+c*j, and the state at time j+2 differs by 2c.
// Both divisors divide 2c, so a hit occurs at some time if and only if it
// occurs before time 2. The printed counts are exact on that grid. They do
// not show that every integer hits, and they do not show that a uniform
// core applies.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Grid bounds. Seeds run through [-20, 20]. Offsets run through [-4, 4].
// The two divisors are ±2. The exhaustive horizon is |D|=2. A second scan
// through time 7 checks that no later hit appears without an early one.
// Every state used below has absolute value at most 20+4*7 = 48.
const (
	seedMin        = int64(-20)
	seedMax        = int64(20)
	offsetMin      = int64(-4)
	offsetMax      = int64(4)
	earlyHorizon   = 2
	scanHorizon    = 8
	uniformWorkers = 4
	uniformQ       = int64(1)
)

// Totals counts comparisons, hits, misses, and disagreements.
type Totals struct {
	Checks   uint64
	Hits     uint64
	Misses   uint64
	Failures uint64
}

// Add accumulates a worker total into the receiver.
func (t *Totals) Add(other Totals) {
	t.Checks += other.Checks
	t.Hits += other.Hits
	t.Misses += other.Misses
	t.Failures += other.Failures
}

// Workspace holds q^j and the offset sum through the scan horizon.
// Load refills the existing buffers. A workspace is not safe for
// concurrent calls.
type Workspace struct {
	Pow  []int64
	Trap []int64
}

// Cache holds the two signed divisors of the uniform grid.
type Cache struct {
	Divisors [2]int64
}

// NewWorkspace allocates the power and offset buffers once.
func NewWorkspace() *Workspace {
	return &Workspace{
		Pow:  make([]int64, scanHorizon),
		Trap: make([]int64, scanHorizon),
	}
}

// NewCache returns the divisors ±2.
func NewCache() *Cache {
	return &Cache{Divisors: [2]int64{-2, 2}}
}

// Abs64 returns the absolute value. Callers stay away from the most
// negative int64.
func Abs64(x int64) int64 {
	if x < 0 {
		return -x
	}
	return x
}

// Divides reports whether d divides n. The caller passes a nonzero d.
func Divides(d, n int64) bool {
	return n%d == 0
}

// MulOK returns a*b when the product fits in int64.
func MulOK(a, b int64) (int64, bool) {
	if a == 0 || b == 0 {
		return 0, true
	}
	const minInt64 = -1 << 63
	if (a == -1 && b == minInt64) || (b == -1 && a == minInt64) {
		return 0, false
	}
	prod := a * b
	if prod/a != b {
		return 0, false
	}
	return prod, true
}

// AddOK returns a+b when the sum fits in int64.
func AddOK(a, b int64) (int64, bool) {
	sum := a + b
	if (sum > a) != (b > 0) && b != 0 {
		return 0, false
	}
	return sum, true
}

// Load fills q^j and the sum of q^0 through q^(j-1). The empty power is 1
// and the empty sum is 0. It returns false when a power overflows.
func (w *Workspace) Load(q int64) bool {
	pow := int64(1)
	trap := int64(0)
	ps := w.Pow[:len(w.Pow)]
	ts := w.Trap[:len(w.Trap)]
	for j := 0; j < len(ps); j++ {
		ps[j] = pow
		ts[j] = trap
		nextPow, okPow := MulOK(pow, q)
		if !okPow {
			return false
		}
		nextTrap, okTrap := AddOK(trap, pow)
		if !okTrap {
			return false
		}
		pow = nextPow
		trap = nextTrap
	}
	return true
}

// State returns q^j*n + c*U_j(q) from the loaded buffers.
func (w *Workspace) State(c, n int64, j int) (int64, bool) {
	term, okTerm := MulOK(w.Pow[j], n)
	if !okTerm {
		return 0, false
	}
	off, okOff := MulOK(c, w.Trap[j])
	if !okOff {
		return 0, false
	}
	return AddOK(term, off)
}

// ClosedState is the multiplier-one state n+c*j, with no power table.
func ClosedState(c, n int64, j int) (int64, bool) {
	off, ok := MulOK(c, int64(j))
	if !ok {
		return 0, false
	}
	return AddOK(n, off)
}

// IsFirstHit reports that j is the least time at which d divides the
// affine state. The scan stops at scanHorizon. A time at or beyond that
// horizon is reported as a miss, which is a grid limitation outside the
// multiplier-one argument.
func IsFirstHit(w *Workspace, q, c, d, n int64, j int) bool {
	if j < 0 || j >= scanHorizon || !w.Load(q) {
		return false
	}
	for i := 0; i <= j; i++ {
		state, ok := w.State(c, n, i)
		if !ok {
			return false
		}
		if !Divides(d, state) {
			if i == j {
				return false
			}
			continue
		}
		return i == j
	}
	return false
}

// FirstEarly returns the least hit strictly before earlyHorizon, if any.
func (w *Workspace) FirstEarly(c, d, n int64) (int, bool, bool) {
	for j := 0; j < earlyHorizon; j++ {
		state, ok := w.State(c, n, j)
		if !ok {
			return 0, false, false
		}
		if Divides(d, state) {
			return j, true, true
		}
	}
	return 0, false, true
}

// SweepOne counts hits of one offset and divisor on an inclusive seed
// interval. A hit after the early horizon, or a disagreement between the
// power table and n+c*j, is a failure.
func (w *Workspace) SweepOne(c, d, lo, hi int64) Totals {
	var tot Totals
	if !w.Load(uniformQ) {
		tot.Failures++
		return tot
	}
	for n := lo; n <= hi; n++ {
		hit := false
		for j := 0; j < scanHorizon; j++ {
			state, ok := w.State(c, n, j)
			tot.Checks++
			if !ok {
				tot.Failures++
				return tot
			}
			closed, okClosed := ClosedState(c, n, j)
			tot.Checks++
			if !okClosed || state != closed {
				tot.Failures++
				return tot
			}
			if Divides(d, state) {
				if j < earlyHorizon {
					hit = true
				} else {
					tot.Failures++
				}
				break
			}
		}
		if hit {
			tot.Hits++
		} else {
			tot.Misses++
		}
	}
	return tot
}

// Sweep runs the multiplier-one grid for both cached divisors.
// Independent seed blocks run in separate goroutines.
func Sweep(cache *Cache) Totals {
	var totals Totals
	var mu sync.Mutex
	for _, d := range cache.Divisors {
		for c := offsetMin; c <= offsetMax; c++ {
			var wg sync.WaitGroup
			span := seedMax - seedMin + 1
			width := (span + uniformWorkers - 1) / uniformWorkers
			for worker := 0; worker < uniformWorkers; worker++ {
				lo := seedMin + int64(worker)*width
				if lo > seedMax {
					continue
				}
				hi := lo + width - 1
				if hi > seedMax {
					hi = seedMax
				}
				wg.Add(1)
				go func(c, d, lo, hi int64) {
					defer wg.Done()
					w := NewWorkspace()
					part := w.SweepOne(c, d, lo, hi)
					mu.Lock()
					totals.Add(part)
					mu.Unlock()
				}(c, d, lo, hi)
			}
			wg.Wait()
		}
	}
	return totals
}

// PureBoundOK reports the slope-one comparison on one divisible seed.
// It returns false when d does not divide n, including the seed 1.
func PureBoundOK(d, n int64) bool {
	if d == 0 || !Divides(d, n) {
		return false
	}
	quot := n / d
	return Abs64(d)*Abs64(quot) <= Abs64(n)
}

// main prints the finite hit count. A positive failure count exits nonzero.
// The last line refuses the universal reading of the grid.
func main() {
	totals := Sweep(NewCache())
	fmt.Printf(
		"q=%d divisors=±2 seeds=%d..%d offsets=%d..%d\n",
		uniformQ, seedMin, seedMax, offsetMin, offsetMax,
	)
	fmt.Printf(
		"hits=%d misses=%d checks=%d failures=%d\n",
		totals.Hits, totals.Misses, totals.Checks, totals.Failures,
	)
	fmt.Println(
		"Finite grid only: not every integer is shown to hit, " +
			"and a uniform core is not obtained.",
	)
	if totals.Failures != 0 {
		os.Exit(1)
	}
}
