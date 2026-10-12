// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"fmt"
	"os"
	"sync"
)

// Step applies one positive offset step to a machine-word state.
func Step(c, n uint64) uint64 {
	if n%2 == 0 {
		return n / 2
	}
	return 3*n + c
}

// Gcd returns the Euclidean greatest common divisor of two machine words.
func Gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// Pow3 returns three to the power a, valid for a at most forty.
func Pow3(a uint64) uint64 {
	power := uint64(1)
	for i := uint64(0); i < a; i++ {
		power *= 3
	}
	return power
}

// Workspace owns the reusable orbit buffer of one worker and is not goroutine safe.
type Workspace struct {
	orbit []uint64
}

// NewWorkspace allocates an orbit buffer with the given capacity.
func NewWorkspace(capacity int) *Workspace {
	return &Workspace{orbit: make([]uint64, 0, capacity)}
}

// Orbit fills the workspace buffer with the first horizon states of the orbit of seed and
// returns that buffer view. Callers keep the horizon short enough that the machine words stay
// exact. The view is invalidated by the next call on the workspace.
func (w *Workspace) Orbit(c, seed uint64, horizon int) []uint64 {
	w.orbit = w.orbit[:0]
	state := seed
	for i := 0; i < horizon; i++ {
		w.orbit = append(w.orbit, state)
		state = Step(c, state)
	}
	return w.orbit
}

// Cache records moduli whose gcd preservation was checked, so that a sweep verifies each
// stratum once while still testing every seed.
type Cache struct {
	verified map[uint64]bool
}

// NewCache returns an empty verification cache.
func NewCache() *Cache {
	return &Cache{verified: make(map[uint64]bool)}
}

// Mark records that the stratum of the given modulus was verified.
func (c *Cache) Mark(m uint64) {
	c.verified[m] = true
}

// Seen reports whether the stratum of the given modulus was verified before.
func (c *Cache) Seen(m uint64) bool {
	return c.verified[m]
}

// StratumPreserved reports whether one offset step preserves the gcd with m on every state
// below horizon, and returns the first violating state, or zero when none exists.
func StratumPreserved(c, m, horizon uint64) (bool, uint64) {
	for n := uint64(0); n < horizon; n++ {
		if Gcd(Step(c, n), m) != Gcd(n, m) {
			return false, n
		}
	}
	return true, 0
}

// OrbitStratumPreserved reports whether every state of the orbit of seed up to horizon keeps
// the seed gcd with m.
func OrbitStratumPreserved(c, m, seed uint64, horizon int, ws *Workspace) bool {
	want := Gcd(seed, m)
	states := ws.Orbit(c, seed, horizon)
	states = states[:len(states)]
	for i := 0; i < len(states); i++ {
		if Gcd(states[i], m) != want {
			return false
		}
	}
	return true
}

// CycleWitness reports whether c, 4c and 2c form the exact three-step cycle of an odd offset.
func CycleWitness(c uint64) bool {
	if c%2 == 0 {
		return false
	}
	return Step(c, c) == 4*c && Step(c, 4*c) == 2*c && Step(c, 2*c) == c
}

// AvoidsCycle reports whether the first horizon states of the orbit of seed avoid c, 4c and 2c.
func AvoidsCycle(c, seed uint64, horizon int, ws *Workspace) bool {
	states := ws.Orbit(c, seed, horizon)
	states = states[:len(states)]
	for i := 0; i < len(states); i++ {
		if states[i] == c || states[i] == 4*c || states[i] == 2*c {
			return false
		}
	}
	return true
}

// MultiplesBelow counts the multiples of m in the half-open range from zero to n. A zero
// modulus lies outside the mathematical domain and contributes nothing.
func MultiplesBelow(m, n uint64) uint64 {
	if m == 0 {
		return 0
	}
	return (n + m - 1) / m
}

// DensityHolds reports whether multiples of m below n satisfy m * count at most n + m.
func DensityHolds(m, n uint64) bool {
	return m*MultiplesBelow(m, n) <= n+m
}

// HalvingPrefix returns the state reached from 2^v * u after exactly v halving steps.
func HalvingPrefix(c, u uint64, v int, ws *Workspace) uint64 {
	states := ws.Orbit(c, u<<uint(v), v+1)
	states = states[:len(states)]
	return states[len(states)-1]
}

// Reaches reports whether the orbit of seed exceeds bound within the first budget steps. The
// walk stops at the first state above the bound, so no state beyond it is computed and no
// machine-word wrap can occur.
func Reaches(c, seed, bound uint64, budget int) bool {
	state := seed
	if state > bound {
		return true
	}
	for i := 0; i < budget; i++ {
		state = Step(c, state)
		if state > bound {
			return true
		}
	}
	return false
}

// ScalingHolds reports whether the first k steps of the offset 3^a on 3^a * n equal 3^a times
// the first k steps of the offset one on n.
func ScalingHolds(a, n uint64, k int) bool {
	power := Pow3(a)
	scaled, plain := power*n, n
	for i := 0; i < k; i++ {
		scaled = Step(power, scaled)
		plain = Step(1, plain)
		if scaled != power*plain {
			return false
		}
	}
	return true
}

// sweepStratumChecks tests one step and whole orbits for every divisor coprime to six.
func sweepStratumChecks(checks, failures *uint64, cache *Cache, ws *Workspace) {
	for c := uint64(1); c <= 200; c++ {
		for m := uint64(2); m <= c; m++ {
			if c%m != 0 || Gcd(m, 6) != 1 {
				continue
			}
			ok, witness := StratumPreserved(c, m, 5000)
			*checks++
			if !ok {
				*failures++
				fmt.Printf("stratum failure: c=%d m=%d n=%d\n", c, m, witness)
			}
			if cache.Seen(m) {
				continue
			}
			cache.Mark(m)
			for seed := uint64(0); seed <= 40; seed++ {
				*checks++
				if !OrbitStratumPreserved(c, m, seed, 12, ws) {
					*failures++
					fmt.Printf("orbit stratum failure: c=%d m=%d seed=%d\n", c, m, seed)
				}
			}
		}
	}
}

// sweepCycleChecks tests the cycle and its avoidance by coprime seeds.
func sweepCycleChecks(checks, failures *uint64, ws *Workspace) {
	for c := uint64(1); c <= 400; c++ {
		if c%2 == 0 {
			continue
		}
		*checks++
		if !CycleWitness(c) {
			*failures++
			fmt.Printf("cycle failure: c=%d\n", c)
		}
		for m := uint64(2); m <= c; m++ {
			if c%m != 0 || Gcd(m, 6) != 1 {
				continue
			}
			*checks++
			if !AvoidsCycle(c, 1, 64, ws) {
				*failures++
				fmt.Printf("seed one joins the cycle: c=%d m=%d\n", c, m)
			}
		}
	}
}

// sweepDensityChecks tests the multiplicity bound on a bounded rectangle of parameters.
func sweepDensityChecks(checks, failures *uint64) {
	for m := uint64(1); m <= 64; m++ {
		for n := uint64(0); n <= 2000; n++ {
			*checks++
			if !DensityHolds(m, n) {
				*failures++
				fmt.Printf("density failure: m=%d n=%d\n", m, n)
			}
		}
	}
}

// sweepEvenOffsetChecks tests the dyadic prefix and unbounded growth for even offsets.
func sweepEvenOffsetChecks(checks, failures *uint64, ws *Workspace) {
	for _, c := range []uint64{2, 4, 6, 30, 64, 1000} {
		for v := 1; v <= 16; v++ {
			for u := uint64(1); u <= 41; u += 2 {
				*checks++
				if HalvingPrefix(c, u, v, ws) != u {
					*failures++
					fmt.Printf("halving failure: c=%d u=%d v=%d\n", c, u, v)
				}
				*checks++
				if !Reaches(c, u<<uint(v), 1<<20, 64) {
					*failures++
					fmt.Printf("growth failure: c=%d u=%d v=%d\n", c, u, v)
				}
			}
		}
	}
}

// sweepScalingChecks tests the scaled instances c = 3^a.
func sweepScalingChecks(checks, failures *uint64) {
	for a := uint64(1); a <= 8; a++ {
		for n := uint64(1); n <= 200; n++ {
			*checks++
			if !ScalingHolds(a, n, 6) {
				*failures++
				fmt.Printf("scaling failure: a=%d n=%d\n", a, n)
			}
		}
	}
}

// parallelStratumSweep partitions a modulus range over four independent workers.
func parallelStratumSweep(chunks int) (uint64, uint64) {
	var checks, failures uint64
	var mu sync.Mutex
	var group sync.WaitGroup
	for chunk := 0; chunk < chunks; chunk++ {
		group.Add(1)
		go func(chunk int) {
			defer group.Done()
			ws := NewWorkspace(64)
			var localChecks, localFailures uint64
			lo := uint64(chunk)*50 + 1
			hi := lo + 49
			for c := lo; c <= hi; c++ {
				for m := uint64(2); m <= c; m++ {
					if c%m != 0 || Gcd(m, 6) != 1 {
						continue
					}
					localChecks++
					if ok, _ := StratumPreserved(c, m, 2000); !ok {
						localFailures++
					}
					for seed := uint64(1); seed <= 8; seed++ {
						localChecks++
						if !OrbitStratumPreserved(c, m, seed, 10, ws) {
							localFailures++
						}
					}
				}
			}
			mu.Lock()
			checks += localChecks
			failures += localFailures
			mu.Unlock()
		}(chunk)
	}
	group.Wait()
	return checks, failures
}

// main runs the bounded certificate sweep and reports the totals; any failure exits nonzero.
func main() {
	var checks, failures uint64
	cache := NewCache()
	ws := NewWorkspace(128)
	sweepStratumChecks(&checks, &failures, cache, ws)
	sweepCycleChecks(&checks, &failures, ws)
	sweepDensityChecks(&checks, &failures)
	sweepEvenOffsetChecks(&checks, &failures, ws)
	sweepScalingChecks(&checks, &failures)
	parallelChecks, parallelFailures := parallelStratumSweep(4)
	checks += parallelChecks
	failures += parallelFailures
	fmt.Printf("offset obstruction checks: %d, failures: %d\n", checks, failures)
	if failures != 0 {
		os.Exit(1)
	}
}
