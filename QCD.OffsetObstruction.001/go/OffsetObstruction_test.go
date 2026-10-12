// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// nextState advances a deterministic 64-bit linear congruential generator.
func nextState(state uint64) uint64 {
	return state*6364136223846793005 + 1442695040888963407
}

// referenceStep recomputes one offset step with arbitrary-precision arithmetic.
func referenceStep(c, n uint64) *big.Int {
	cBig, nBig := new(big.Int).SetUint64(c), new(big.Int).SetUint64(n)
	half := new(big.Int).Rsh(nBig, 1)
	if nBig.Bit(0) == 0 {
		return half
	}
	triple := new(big.Int).Mul(nBig, big.NewInt(3))
	return triple.Add(triple, cBig)
}

// TestStepMatchesReference cross-checks the machine-word step against big-integer arithmetic.
func TestStepMatchesReference(t *testing.T) {
	state := uint64(1)
	for i := 0; i < 20000; i++ {
		state = nextState(state)
		c := state%1000 + 1
		n := (state >> 10) % (1 << 40)
		if Step(c, n) != referenceStep(c, n).Uint64() {
			t.Fatalf("step mismatch at c=%d n=%d", c, n)
		}
	}
}

// TestStratumPreservation checks one-step and orbit invariance, with a negative control for a
// modulus that does not divide the offset.
func TestStratumPreservation(t *testing.T) {
	ws := NewWorkspace(64)
	for c := uint64(1); c <= 150; c++ {
		for m := uint64(2); m <= c; m++ {
			if c%m != 0 || Gcd(m, 6) != 1 {
				continue
			}
			if ok, witness := StratumPreserved(c, m, 4000); !ok {
				t.Fatalf("stratum lost at c=%d m=%d n=%d", c, m, witness)
			}
			for seed := uint64(0); seed <= 60; seed++ {
				if !OrbitStratumPreserved(c, m, seed, 10, ws) {
					t.Fatalf("orbit stratum lost at c=%d m=%d seed=%d", c, m, seed)
				}
			}
		}
	}
	// Negative control: m = 5 does not divide c = 1 and invariance already fails at n = 3.
	if ok, witness := StratumPreserved(1, 5, 4); ok || witness != 3 {
		t.Fatalf("expected the first stratum violation at n=3, got ok=%v witness=%d", ok, witness)
	}
}

// TestCycleWitness checks the three-step cycle and its avoidance, with direction controls.
func TestCycleWitness(t *testing.T) {
	ws := NewWorkspace(64)
	for c := uint64(1); c <= 300; c += 2 {
		if !CycleWitness(c) {
			t.Fatalf("cycle missing for odd offset c=%d", c)
		}
		for m := uint64(2); m <= c; m++ {
			if c%m != 0 || Gcd(m, 6) != 1 {
				continue
			}
			if !AvoidsCycle(c, 1, 64, ws) {
				t.Fatalf("seed one entered the cycle at c=%d m=%d", c, m)
			}
		}
	}
	// Negative control: an even offset has no such cycle at its own value.
	if CycleWitness(4) {
		t.Fatal("even offset reported an odd-cycle witness")
	}
	// Negative control: the seed 4c is a cycle state and must be detected.
	if AvoidsCycle(3, 12, 16, ws) {
		t.Fatal("cycle state 4c was not detected by the avoidance scan")
	}
}

// TestMultiplesBelow checks the counting formula against brute force and the density bound.
func TestMultiplesBelow(t *testing.T) {
	for m := uint64(1); m <= 40; m++ {
		for n := uint64(0); n <= 400; n++ {
			var brute uint64
			for value := uint64(0); value < n; value++ {
				if value%m == 0 {
					brute++
				}
			}
			if MultiplesBelow(m, n) != brute {
				t.Fatalf("count mismatch m=%d n=%d: %d != %d", m, n, MultiplesBelow(m, n), brute)
			}
			if !DensityHolds(m, n) {
				t.Fatalf("density bound failed at m=%d n=%d", m, n)
			}
		}
	}
	// Negative control: the sharper bound without the additive slack fails at m=2, n=5.
	if 2*MultiplesBelow(2, 5) <= 5 {
		t.Fatal("control bound unexpectedly held")
	}
}

// TestHalvingAndGrowth checks the exact dyadic prefix and unbounded growth for even offsets.
func TestHalvingAndGrowth(t *testing.T) {
	ws := NewWorkspace(128)
	for _, c := range []uint64{2, 8, 42, 1000} {
		for v := 1; v <= 20; v++ {
			for u := uint64(1); u <= 31; u += 2 {
				if got := HalvingPrefix(c, u, v, ws); got != u {
					t.Fatalf("halving mismatch c=%d u=%d v=%d: got %d", c, u, v, got)
				}
				if !Reaches(c, u<<uint(v), 1<<24, 80) {
					t.Fatalf("growth stalled at c=%d u=%d v=%d", c, u, v)
				}
			}
		}
	}
	// Negative control: an odd offset need not grow without bound from every seed.
	if Reaches(1, 1, 1<<20, 64) {
		t.Fatal("odd offset control seed unexpectedly exceeded the bound")
	}
}

// TestScalingIdentity compares the scaled dynamics against big-integer arithmetic.
func TestScalingIdentity(t *testing.T) {
	for a := uint64(1); a <= 10; a++ {
		power := Pow3(a)
		for n := uint64(1); n <= 120; n++ {
			scaled, plain := power*n, n
			for k := 0; k < 6; k++ {
				if scaled != power*plain {
					t.Fatalf("scaling mismatch a=%d n=%d k=%d", a, n, k)
				}
				scaled = Step(power, scaled)
				plain = Step(1, plain)
			}
			if !ScalingHolds(a, n, 6) {
				t.Fatalf("scaling claim failed at a=%d n=%d", a, n)
			}
		}
	}
}

// TestParallelSweepAgrees checks that the partitioned workers reproduce a sequential count.
func TestParallelSweepAgrees(t *testing.T) {
	parallelChecks, parallelFailures := parallelStratumSweep(4)
	var pairs uint64
	for c := uint64(1); c <= 200; c++ {
		for m := uint64(2); m <= c; m++ {
			if c%m == 0 && Gcd(m, 6) == 1 {
				pairs++
			}
		}
	}
	// Every pair contributes one one-step check and eight orbit checks.
	sequential := pairs * 9
	if parallelChecks != sequential || parallelFailures != 0 {
		t.Fatalf("parallel sweep mismatch: checks=%d want=%d failures=%d",
			parallelChecks, sequential, parallelFailures)
	}
}

// TestWarmedOrbitAllocation checks that a warmed workspace traversal allocates nothing.
func TestWarmedOrbitAllocation(t *testing.T) {
	ws := NewWorkspace(64)
	ws.Orbit(7, 3, 32)
	allocs := testing.AllocsPerRun(100, func() {
		ws.Orbit(7, 3, 32)
	})
	if allocs != 0 {
		t.Fatalf("warmed orbit allocated %v times per run", allocs)
	}
}

// TestCacheSemantics checks that the stratum cache records and reports moduli.
func TestCacheSemantics(t *testing.T) {
	cache := NewCache()
	if cache.Seen(9) {
		t.Fatal("cache reported an unseen modulus")
	}
	cache.Mark(9)
	if !cache.Seen(9) {
		t.Fatal("cache lost a marked modulus")
	}
}
