// SPDX-License-Identifier: CC-BY-4.0
//
// Tests for the exact certificate of QCD.Relations.Cycles.001. Every test
// recomputes its subject with an independent math/big implementation, so a
// buffer error inside the workspace cannot agree with the reference by
// accident.

package main

import (
	"math/big"
	"testing"
)

// referenceStep computes one instruction of the raw map with freshly allocated
// math/big values, independent of the workspace buffers.
func referenceStep(d, q, c, n int64) *big.Int {
	dBig := big.NewInt(d)
	if new(big.Int).Mod(big.NewInt(n), dBig).Sign() == 0 {
		return new(big.Int).Quo(big.NewInt(n), dBig)
	}
	return new(big.Int).Add(new(big.Int).Mul(big.NewInt(q), big.NewInt(n)), big.NewInt(c))
}

// referenceStepBig computes one raw step with full-width operands, so a walk
// longer than the machine word keeps exact values.
func referenceStepBig(d, q, c, n *big.Int) *big.Int {
	if new(big.Int).Mod(n, d).Sign() == 0 {
		return new(big.Int).Quo(n, d)
	}
	return new(big.Int).Add(new(big.Int).Mul(q, n), c)
}

// TestStepMatchesReference compares the uint64 step with the reference on a
// grid that covers divisible and non-divisible states.
func TestStepMatchesReference(t *testing.T) {
	for d := uint64(2); d <= 12; d++ {
		for q := uint64(1); q <= 9; q++ {
			for c := uint64(0); c <= 9; c++ {
				for n := uint64(0); n <= 40; n++ {
					got := new(big.Int).SetUint64(Step(d, q, c, n))
					want := referenceStep(int64(d), int64(q), int64(c), int64(n))
					if got.Cmp(want) != 0 {
						t.Fatalf("Step(%d,%d,%d,%d) = %s, want %s",
							d, q, c, n, got, want)
					}
				}
			}
		}
	}
}

// TestStepBigMatchesReference compares the workspace step, including states
// beyond machine words, with the reference.
func TestStepBigMatchesReference(t *testing.T) {
	w := NewWorkspace()
	for d := uint64(2); d <= 7; d++ {
		for q := uint64(3); q <= 11; q += 2 {
			for c := uint64(1); c <= 5; c++ {
				w.SetParams(d, q, c)
				for n := int64(0); n <= 60; n++ {
					w.Cur.SetInt64(n)
					got := w.StepBig(w.Cur, w.Next)
					want := referenceStep(int64(d), int64(q), int64(c), n)
					if got.Cmp(want) != 0 {
						t.Fatalf("StepBig(%d,%d,%d,%d) = %s, want %s",
							d, q, c, n, got, want)
					}
				}
			}
		}
	}
	w.SetParams(2, 3, 1)
	w.Cur.SetString("123456789012345678901234567890", 10)
	got := new(big.Int).Set(w.StepBig(w.Cur, w.Next))
	want := referenceStepBig(big.NewInt(2), big.NewInt(3), big.NewInt(1), w.Cur)
	if got.Cmp(want) != 0 {
		t.Fatalf("large StepBig = %s, want %s", got, want)
	}
}

// TestCycleSliceTriples checks the first three triples of the first slice and
// the cycle length 3h+1 by independent iteration.
func TestCycleSliceTriples(t *testing.T) {
	w := NewWorkspace()
	wantC := []uint64{3, 27, 219}
	wantQ := []uint64{7, 55, 439}
	for i, h := range []uint64{1, 2, 3} {
		c, q := w.CycleOffsets(h)
		if c.Uint64() != wantC[i] || q.Uint64() != wantQ[i] {
			t.Fatalf("h=%d gives (q,c)=(%s,%s), want (%d,%d)",
				h, q, c, wantQ[i], wantC[i])
		}
		// Seven times the offset is three times 8^h - 1.
		lhs := new(big.Int).Mul(c, big.NewInt(7))
		rhs := new(big.Int).Sub(new(big.Int).Lsh(big.NewInt(1), uint(3*h)), big.NewInt(1))
		rhs.Mul(rhs, big.NewInt(3))
		if lhs.Cmp(rhs) != 0 {
			t.Fatalf("7c = 3(8^%d - 1) failed: %s vs %s", h, lhs, rhs)
		}
		// The affine step of 3 lands on 3 * 2^(3h).
		top := referenceStep(2, int64(q.Uint64()), int64(c.Uint64()), 3)
		wantTop := new(big.Int).Lsh(big.NewInt(3), uint(3*h))
		if top.Cmp(wantTop) != 0 {
			t.Fatalf("affine step at h=%d = %s, want %s", h, top, wantTop)
		}
		// The orbit returns to 3 exactly after 3h+1 steps.
		cur := big.NewInt(3)
		length := 0
		for length < int(4*h+4) {
			cur = referenceStep(2, int64(q.Uint64()), int64(c.Uint64()), cur.Int64())
			length++
			if cur.Cmp(big.NewInt(3)) == 0 {
				break
			}
			if cur.Cmp(big.NewInt(1)) == 0 {
				t.Fatalf("h=%d cycle contains 1 at step %d", h, length)
			}
		}
		if length != int(3*h+1) {
			t.Fatalf("h=%d returns after %d steps, want %d", h, length, 3*h+1)
		}
	}
}

// TestFullAccessResiduesAndIdentity recomputes the third slice independently
// and checks the residue agreement and the defining identity.
func TestFullAccessResiduesAndIdentity(t *testing.T) {
	for d := int64(2); d <= fullAccessMaxD; d++ {
		for k := int64(2); k <= fullAccessMaxK; k++ {
			base := new(big.Int).Exp(big.NewInt(d), big.NewInt(k-1), nil)
			c := new(big.Int).Sub(base, big.NewInt(1))
			c.Mul(c, big.NewInt(d-1))
			q := new(big.Int).Mul(base, big.NewInt(d-1))
			q.Add(q, big.NewInt(1))
			if new(big.Int).Mod(q, big.NewInt(d)).Cmp(big.NewInt(1)) != 0 {
				t.Fatalf("q not 1 mod %d at k=%d", d, k)
			}
			if new(big.Int).Mod(c, big.NewInt(d)).Cmp(big.NewInt(1)) != 0 {
				t.Fatalf("c not 1 mod %d at k=%d", d, k)
			}
			lhs := new(big.Int).Mul(q, big.NewInt(d-1))
			lhs.Add(lhs, c)
			rhs := new(big.Int).Mul(base, big.NewInt(d))
			rhs.Mul(rhs, big.NewInt(d-1))
			if lhs.Cmp(rhs) != 0 {
				t.Fatalf("identity failed at d=%d k=%d: %s vs %s", d, k, lhs, rhs)
			}
		}
	}
}

// TestIntersectionEquivalence recomputes the fourth slice independently: over
// the checked seeds and times a state reaches 1 exactly when it is the
// corresponding power of d.
func TestIntersectionEquivalence(t *testing.T) {
	one := big.NewInt(1)
	for d := int64(3); d <= 12; d++ {
		dBig := big.NewInt(d)
		qBig := big.NewInt(d + 1)
		cBig := big.NewInt(d - 1)
		for x := int64(1); x <= 200; x++ {
			cur := big.NewInt(x)
			for j := int64(0); j <= 16; j++ {
				hit := cur.Cmp(one) == 0
				pow := new(big.Int).Exp(dBig, big.NewInt(j), nil)
				if hit != (pow.Cmp(big.NewInt(x)) == 0) {
					t.Fatalf("equivalence failed at d=%d x=%d j=%d", d, x, j)
				}
				cur = referenceStepBig(dBig, qBig, cBig, cur)
			}
		}
	}
	// The state 1 never returns to itself at a positive time.
	cur := big.NewInt(1)
	for j := 1; j <= 8; j++ {
		cur = referenceStepBig(big.NewInt(3), big.NewInt(4), big.NewInt(2), cur)
		if cur.Cmp(one) == 0 {
			t.Fatalf("d=3 returned 1 to itself at time %d", j)
		}
	}
}

// TestIntersectionControlAtTwo records that the equivalence of the fourth
// slice needs d >= 3: at d = 2 the seed 3 reaches 1 without being a power of 2.
func TestIntersectionControlAtTwo(t *testing.T) {
	cur := big.NewInt(3)
	reached := false
	for j := 0; j <= 24; j++ {
		if cur.Cmp(big.NewInt(1)) == 0 {
			reached = true
			break
		}
		cur = referenceStep(2, 3, 1, cur.Int64())
	}
	if !reached {
		t.Fatalf("d=2 control: 3 did not reach 1")
	}
	for j := 0; j <= 24; j++ {
		if new(big.Int).Exp(big.NewInt(2), big.NewInt(int64(j)), nil).Cmp(big.NewInt(3)) == 0 {
			t.Fatalf("d=2 control: 3 is a power of 2 at exponent %d", j)
		}
	}
}

// TestEvenOffsetGrowthControl checks the d = 2 slice with an even offset: the
// reach to an odd state and the strict growth afterwards, and the c = 0
// boundary where the seed 1 is fixed.
func TestEvenOffsetGrowthControl(t *testing.T) {
	two := big.NewInt(2)
	for c := int64(2); c <= 6; c += 2 {
		qBig := big.NewInt(2*c + 1)
		cBig := big.NewInt(c)
		for n := int64(1); n <= 50; n++ {
			cur := big.NewInt(n)
			steps := 0
			for cur.Bit(0) == 0 && steps <= evenOffsetReach {
				cur = referenceStepBig(two, qBig, cBig, cur)
				steps++
			}
			if steps > evenOffsetReach || cur.Bit(0) != 1 {
				t.Fatalf("c=%d seed %d did not reach an odd state", c, n)
			}
			for i := 0; i < 32; i++ {
				next := referenceStepBig(two, qBig, cBig, cur)
				if next.Bit(0) != 1 || next.Cmp(cur) <= 0 {
					t.Fatalf("c=%d seed %d growth failed at step %d", c, n, i)
				}
				cur = next
			}
		}
	}
	// With c = 0 the affine step is the identity on odd states, so the growth
	// statement needs c >= 1.
	if got := referenceStep(2, 1, 0, 1); got.Cmp(big.NewInt(1)) != 0 {
		t.Fatalf("c=0 control: step of 1 = %s, want 1", got)
	}
}

// TestOddOffsetGcdControl checks the gcd invariance of the d = 2 slice with an
// odd offset, the realization of every divisor stratum, and the failure at an
// even offset.
func TestOddOffsetGcdControl(t *testing.T) {
	for c := uint64(1); c <= oddOffsetMaxC; c += 2 {
		q := 2*c + 1
		for n := uint64(1); n <= 300; n++ {
			if Gcd(Step(2, q, c, n), c) != Gcd(n, c) {
				t.Fatalf("gcd not preserved at c=%d n=%d", c, n)
			}
		}
		for e := uint64(1); e <= c; e++ {
			if c%e != 0 {
				continue
			}
			found := false
			for n := uint64(1); n <= 200 && !found; n++ {
				found = Gcd(n, c) == e
			}
			if !found {
				t.Fatalf("stratum %d of c=%d not realized", e, c)
			}
		}
	}
	// At the even offset c = 2 the invariance fails at n = 2.
	if Gcd(Step(2, 5, 2, 2), 2) == Gcd(2, 2) {
		t.Fatalf("even-offset control: gcd invariance unexpectedly holds")
	}
}

// TestOddOffsetSeedCapture walks the seed c of every odd offset with c > 1 and
// requires it to avoid 1, which is the finite shadow of the exclusion of the
// seed c from the stratum of 1. The offset c = 1 is the excluded control: its
// seed is 1 itself.
func TestOddOffsetSeedCapture(t *testing.T) {
	w := NewWorkspace()
	for c := uint64(3); c <= oddOffsetMaxC; c += 2 {
		w.SetParams(2, 2*c+1, c)
		w.Cur.SetUint64(c)
		for k := 0; k < oddOffsetCaptureSteps; k++ {
			w.StepBig(w.Cur, w.Next)
			w.Cur, w.Next = w.Next, w.Cur
			if w.Cur.Cmp(BigOne) == 0 {
				t.Fatalf("seed %d of c=%d reached 1 at step %d", c, c, k+1)
			}
		}
	}
	w.SetParams(2, 3, 1)
	w.Cur.SetUint64(1)
	if w.Cur.Cmp(BigOne) != 0 {
		t.Fatalf("control: the seed of c=1 is not 1")
	}
}

// TestSweepTotals pins the printed certificate and its per-slice
// decomposition, and checks that repeating every sweep reproduces them, so
// the reported count cannot drift silently.
func TestSweepTotals(t *testing.T) {
	// Recorded in the family README; each slice is rerun below and compared.
	wantSlices := []uint64{4370, 11935, 569964, 2600000, 43335}
	sweeps := []func() SliceTotals{
		sweepCycleSlice,
		sweepFullAccess,
		sweepIntersection,
		sweepEvenOffset,
		sweepOddOffset,
	}
	var total, repeat SliceTotals
	for i, sweep := range sweeps {
		tot := sweep()
		if tot.Failures != 0 || tot.Checks != wantSlices[i] {
			t.Fatalf("slice %d counted %+v, want checks %d and no failures",
				i, tot, wantSlices[i])
		}
		total.Checks += tot.Checks
		repeat.Checks += sweep().Checks
	}
	if total.Checks != 3229604 {
		t.Fatalf("certificate total %d, want 3229604", total.Checks)
	}
	if repeat.Checks != total.Checks {
		t.Fatalf("second run counted %d checks, first run %d", repeat.Checks, total.Checks)
	}
}

// TestWarmedOrbitAllocation requires the workspace walk to allocate nothing
// after warm-up, which keeps the sweeps free of hidden per-step allocation.
func TestWarmedOrbitAllocation(t *testing.T) {
	w := NewWorkspace()
	w.SetParams(3, 4, 2)
	allocs := testing.AllocsPerRun(50, func() {
		w.Cur.SetUint64(5)
		for i := 0; i < 32; i++ {
			w.StepBig(w.Cur, w.Next)
			w.Cur, w.Next = w.Next, w.Cur
		}
	})
	if allocs != 0 {
		t.Fatalf("orbit walk allocated %v values per run", allocs)
	}
}

// TestDocumentedRanges checks the two claims the sweeps make about their own
// arithmetic: the uint64 sweep stays far below its word limit, while the first
// slice already needs states beyond uint64.
func TestDocumentedRanges(t *testing.T) {
	maxUint64State := uint64(oddOffsetSeeds)*(2*oddOffsetMaxC+1) + oddOffsetMaxC
	if maxUint64State >= 1<<40 {
		t.Fatalf("uint64 sweep reaches %d, beyond the documented range", maxUint64State)
	}
	w := NewWorkspace()
	c, _ := w.CycleOffsets(cycleSliceMaxH)
	if c.BitLen() <= 64 {
		t.Fatalf("first slice at h=%d fits in uint64, so the big path is untested",
			cycleSliceMaxH)
	}
}
