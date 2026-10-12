// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// TestsTotalChecks is the number of bounded certificate checks the main sweep reports.
const TestsTotalChecks = 186207

// nextState advances a deterministic 64-bit linear congruential generator.
func nextState(state uint64) uint64 {
	return state*6364136223846793005 + 1442695040888963407
}

// referenceStep recomputes one plain instruction with arbitrary-precision arithmetic. The result
// is compared against a machine word, so the caller keeps d, c and n small enough that the affine
// value stays below 2^64; Uint64 then truncates nothing.
func referenceStep(d, c, n uint64) *big.Int {
	dBig := new(big.Int).SetUint64(d)
	nBig := new(big.Int).SetUint64(n)
	if new(big.Int).Mod(nBig, dBig).Sign() == 0 {
		return nBig.Div(nBig, dBig)
	}
	mul := new(big.Int).Mul(new(big.Int).Sub(dBig, big.NewInt(1)), nBig)
	return mul.Add(mul, new(big.Int).SetUint64(c))
}

// referenceReturn recomputes one return step with arbitrary-precision arithmetic.
func referenceReturn(d, c, n uint64) *big.Int {
	dBig := new(big.Int).SetUint64(d)
	nBig := new(big.Int).SetUint64(n)
	if n%d == 0 {
		return nBig.Div(nBig, dBig)
	}
	mul := new(big.Int).Mul(new(big.Int).Sub(dBig, big.NewInt(1)), nBig)
	mul.Add(mul, new(big.Int).SetUint64(c))
	return mul.Div(mul, dBig)
}

// TestStepMatchesReference cross-checks the machine-word instruction against big-integer
// arithmetic on random parameters.
func TestStepMatchesReference(t *testing.T) {
	state := uint64(7)
	for i := 0; i < 20000; i++ {
		state = nextState(state)
		d := state%9 + 2
		c := state%13 + 1
		n := state % 5000
		got := new(big.Int).SetUint64(CoreStep(d, c, n))
		if got.Cmp(referenceStep(d, c, n)) != 0 {
			t.Fatalf("step mismatch: d=%d c=%d n=%d got=%s", d, c, n, got)
		}
	}
}

// TestDomainCharacterisation verifies that the divisibility characterisation of the domain agrees
// with the definition on a grid, including offsets divisible by the multiplier. The redundant form
// d | n - c enters through the residue of c, not through the residue of n.
func TestDomainCharacterisation(t *testing.T) {
	for d := uint64(2); d <= 12; d++ {
		for c := uint64(0); c <= 12; c++ {
			for n := uint64(0); n <= 200; n++ {
				want := n%d == 0 || (n+d-c%d)%d == 0
				if CoreInDomain(d, c, n) != want {
					t.Fatalf("domain mismatch: d=%d c=%d n=%d", d, c, n)
				}
				if !ResiduePreserved(d, c, n) {
					t.Fatalf("residue mismatch: d=%d c=%d n=%d", d, c, n)
				}
				next := CoreStep(d, c, n)
				divisible := next%d == 0
				if n%d != 0 && divisible != (n%d == c%d) {
					t.Fatalf("divisibility mismatch: d=%d c=%d n=%d", d, c, n)
				}
			}
		}
	}
}

// TestReturnRealization checks that one return step is realized by one instruction at a multiple
// of d and by two instructions at a residue-c state.
func TestReturnRealization(t *testing.T) {
	for d := uint64(2); d <= 9; d++ {
		for c := uint64(1); c <= 11; c++ {
			for n := uint64(1); n <= 400; n++ {
				if !CoreInDomain(d, c, n) {
					continue
				}
				if !ReturnRealized(d, c, n) {
					t.Fatalf("realization mismatch: d=%d c=%d n=%d", d, c, n)
				}
				steps := CoreReturnSteps(d, c, n)
				if steps != 1 && steps != 2 {
					t.Fatalf("step count: d=%d c=%d n=%d steps=%d", d, c, n, steps)
				}
				want := referenceReturn(d, c, n)
				got := new(big.Int).SetUint64(CoreReturnState(d, c, n))
				if got.Cmp(want) != 0 {
					t.Fatalf("return mismatch: d=%d c=%d n=%d got=%s want=%s", d, c, n, got, want)
				}
			}
		}
	}
}

// TestDescentAndCore checks strict descent above the core and core invariance on the grid.
func TestDescentAndCore(t *testing.T) {
	for d := uint64(2); d <= 9; d++ {
		for c := uint64(1); c <= 11; c++ {
			for n := uint64(1); n <= 500; n++ {
				if n > c && !DescentHolds(d, c, n) {
					t.Fatalf("descent mismatch: d=%d c=%d n=%d", d, c, n)
				}
				if n <= c && !CoreInvariant(d, c, n) {
					t.Fatalf("core mismatch: d=%d c=%d n=%d", d, c, n)
				}
			}
		}
	}
}

// TestReachabilityAndPeriodicity checks that every positive state reaches the core and that the
// core orbit repeats within the core.
func TestReachabilityAndPeriodicity(t *testing.T) {
	w := NewWorkspace(64)
	for d := uint64(2); d <= 9; d++ {
		for c := uint64(1); c <= 11; c++ {
			for n := uint64(1); n <= 500; n++ {
				steps, reached := ReachesCore(d, c, n, 1024)
				if !reached {
					t.Fatalf("reach mismatch: d=%d c=%d n=%d", d, c, n)
				}
				if steps > int(n) {
					t.Fatalf("reach bound: d=%d c=%d n=%d steps=%d", d, c, n, steps)
				}
				core := CoreReturnIterate(d, c, n, steps)
				if core < 1 || core > c {
					t.Fatalf("core range: d=%d c=%d n=%d core=%d", d, c, n, core)
				}
				_, period, ok := w.CorePeriod(d, c, core, int(c)+2)
				if !ok || period == 0 {
					t.Fatalf("period mismatch: d=%d c=%d n=%d", d, c, n)
				}
			}
		}
	}
}

// TestTrapDivergence checks that a state outside the domain keeps growing and stays outside it,
// using arbitrary-precision arithmetic for the reference growth.
func TestTrapDivergence(t *testing.T) {
	state := uint64(11)
	for i := 0; i < 4000; i++ {
		state = nextState(state)
		d := state%8 + 2
		c := state%10 + 1
		n := state%97 + 1
		if CoreInDomain(d, c, n) {
			continue
		}
		if !TrapGrowth(d, c, n, 6) {
			t.Fatalf("trap mismatch: d=%d c=%d n=%d", d, c, n)
		}
		acc := new(big.Int).SetUint64(n)
		prev := new(big.Int).Set(acc)
		for k := 0; k < 6; k++ {
			acc = referenceStep(d, c, acc.Uint64())
			if acc.Cmp(prev) <= 0 {
				t.Fatalf("trap growth: d=%d c=%d n=%d k=%d", d, c, n, k)
			}
			prev = new(big.Int).Set(acc)
		}
	}
}

// TestCornerFamily checks the corner values, the trap range, the raw cycle and the fixed-point
// uniqueness, and records that the value claims already hold at d = 2.
func TestCornerFamily(t *testing.T) {
	for d := uint64(3); d <= 60; d++ {
		if !CornerChecks(d) {
			t.Fatalf("corner mismatch: d=%d", d)
		}
		c := d + 1
		for x := uint64(2); x < d; x++ {
			if CoreInDomain(d, c, x) {
				t.Fatalf("corner trap mismatch: d=%d x=%d", d, x)
			}
		}
	}
	if !ControlChecks() {
		t.Fatal("control mismatch")
	}
	if !CornerChecks(2) {
		t.Fatal("value claims must already hold at d=2")
	}
	if CoreStep(2, 3, 1) != 4 || CoreStep(2, 3, 4) != 2 || CoreStep(2, 3, 2) != 1 {
		t.Fatal("second raw cycle at d=2 missing")
	}
}

// TestRawRealization checks the expansion of domain-closed periodic core orbits to plain cycles
// with arbitrary-precision arithmetic.
func TestRawRealization(t *testing.T) {
	w := NewWorkspace(64)
	for d := uint64(2); d <= 10; d++ {
		for c := uint64(1); c <= 12; c++ {
			for x := uint64(1); x <= c; x++ {
				if !CoreInDomain(d, c, x) {
					continue
				}
				delay, period, ok := w.CorePeriod(d, c, x, int(c)+2)
				if !ok || period == 0 {
					t.Fatalf("core period: d=%d c=%d x=%d", d, c, x)
				}
				start := CoreReturnIterate(d, c, x, delay)
				if _, cycle, cycleOK := w.CorePeriod(d, c, start, int(c)+2); !cycleOK || cycle == 0 {
					t.Fatalf("cycle period: d=%d c=%d x=%d", d, c, x)
				} else {
					period = cycle
				}
				if !DomainClosedPrefix(d, c, start, period) {
					continue
				}
				j, realized := RawRealization(d, c, start, period)
				if !realized || j < period || j > 2*period {
					t.Fatalf("raw realization: d=%d c=%d x=%d p=%d j=%d", d, c, x, period, j)
				}
				want := new(big.Int).SetUint64(CoreReturnIterate(d, c, start, period))
				acc := new(big.Int).SetUint64(start)
				for k := 0; k < j; k++ {
					acc = referenceStep(d, c, acc.Uint64())
				}
				if acc.Cmp(want) != 0 {
					t.Fatalf("realization value: d=%d c=%d x=%d j=%d got=%s want=%s", d, c, x, j, acc, want)
				}
			}
		}
	}
}

// TestSweepTotals pins the reported check total and the contribution of every sweep.
func TestSweepTotals(t *testing.T) {
	var checks, failures uint64
	w := NewWorkspace(64)
	sweepDomainChecks(&checks, &failures)
	if failures != 0 {
		t.Fatalf("domain sweep failures: %d", failures)
	}
	t.Logf("domain checks: %d", checks)
	before := checks
	sweepCoreChecks(&checks, &failures, w)
	t.Logf("core checks: %d", checks-before)
	before = checks
	sweepCornerChecks(&checks, &failures)
	t.Logf("corner checks: %d", checks-before)
	before = checks
	sweepCornerClassificationChecks(&checks, &failures)
	t.Logf("classification checks: %d", checks-before)
	before = checks
	sweepPeriodicPointChecks(&checks, &failures)
	t.Logf("periodic checks: %d", checks-before)
	before = checks
	sweepExpansionChecks(&checks, &failures, w)
	t.Logf("expansion checks: %d", checks-before)
	before = checks
	parallelChecks, parallelFailures := parallelCoreSweep(4, NewCache())
	checks += parallelChecks
	failures += parallelFailures
	t.Logf("parallel checks: %d", checks-before)
	if failures != 0 {
		t.Fatalf("sweep failures: %d", failures)
	}
	if checks != TestsTotalChecks {
		t.Fatalf("total checks: got %d, want %d", checks, TestsTotalChecks)
	}
}

// TestCycleBasinCounts pins the sparse corner-cycle counts below 300000 for the offsets reported
// in the family record, and checks that no seed in those ranges exhausts the classification
// budget.
func TestCycleBasinCounts(t *testing.T) {
	cases := [...]struct {
		d     uint64
		count uint64
	}{
		{3, 1977},
		{4, 63},
		{5, 57},
		{6, 22},
		{7, 31},
		{9, 16},
		{12, 15},
		{20, 10},
	}
	for _, entry := range cases {
		count := CycleBasinCount(entry.d, 300000, 4096)
		if count != entry.count {
			t.Fatalf("basin count: d=%d got %d, want %d", entry.d, count, entry.count)
		}
		for seed := uint64(1); seed < 300000; seed++ {
			if Classify(entry.d, seed, 4096) == 0 {
				t.Fatalf("classification budget expired: d=%d seed=%d", entry.d, seed)
			}
		}
	}
}

// TestCornerClassification checks the two alternatives of the corner classification on explicit
// seeds and the reachable periodic set of short lengths.
func TestCornerClassification(t *testing.T) {
	if Classify(3, 1, 64) != 2 {
		t.Fatal("seed 1 must be a trap at d=3")
	}
	if Classify(3, 4, 64) != 1 {
		t.Fatal("seed 4 must reach the cycle at d=3")
	}
	if Classify(3, 12, 64) != 1 {
		t.Fatal("seed 12 must reach the cycle at d=3")
	}
	for d := uint64(3); d <= 12; d++ {
		for k := 1; k <= 8; k++ {
			for x := uint64(1); x <= 200; x++ {
				state, ok := CoreIterate(d, d+1, x, k)
				fixed := ok && state == x
				onCycle := x == d+1 || x == d*(d+1)
				if fixed != (onCycle && k%2 == 0) {
					t.Fatalf("periodic mismatch: d=%d k=%d x=%d", d, k, x)
				}
			}
		}
	}
	if !TrapGrowth(24, 25, 500, 8) {
		t.Fatal("trap growth must hold on the sweep horizon")
	}
}

// TestParallelSweepAgrees recomputes the chunked sweep serially and compares totals.
func TestParallelSweepAgrees(t *testing.T) {
	parallelChecks, parallelFailures := parallelCoreSweep(4, NewCache())
	var serialChecks, serialFailures uint64
	w := NewWorkspace(64)
	for d := uint64(2); d <= 17; d++ {
		for c := uint64(1); c <= 8; c++ {
			horizon := int(c) + 2
			for n := uint64(1); n <= 200; n++ {
				if !CoreInDomain(d, c, n) {
					continue
				}
				serialChecks++
				if !ReturnRealized(d, c, n) {
					serialFailures++
				}
				if n > c {
					serialChecks++
					if !DescentHolds(d, c, n) {
						serialFailures++
					}
				}
				core := CoreReturnIterate(d, c, n, 1024)
				serialChecks++
				if _, period, ok := w.CorePeriod(d, c, core, horizon); !ok || period == 0 {
					serialFailures++
				}
			}
		}
	}
	if parallelChecks != serialChecks || parallelFailures != serialFailures {
		t.Fatalf("parallel mismatch: checks %d/%d failures %d/%d",
			parallelChecks, serialChecks, parallelFailures, serialFailures)
	}
}

// TestWarmedOrbitAllocation checks that a warmed workspace orbit draw allocates nothing.
func TestWarmedOrbitAllocation(t *testing.T) {
	w := NewWorkspace(64)
	w.CoreOrbit(3, 5, 7, 12)
	allocs := testing.AllocsPerRun(50, func() {
		orbit := w.CoreOrbit(3, 5, 7, 12)
		if len(orbit) != 12 {
			t.Fatal("orbit length")
		}
	})
	if allocs != 0 {
		t.Fatalf("warmed allocation: %v", allocs)
	}
}

// TestCacheSemantics checks the concurrent cache marks and answers each pair once.
func TestCacheSemantics(t *testing.T) {
	cache := NewCache()
	if cache.Seen(3, 4) {
		t.Fatal("empty cache reported a hit")
	}
	cache.Mark(3, 4)
	if !cache.Seen(3, 4) || cache.Seen(4, 3) {
		t.Fatal("cache key handling")
	}
}
