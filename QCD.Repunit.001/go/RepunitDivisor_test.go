// SPDX-License-Identifier: CC-BY-4.0
//
// Tests for the exact certificate of QCD.Repunit.001. The arithmetic of the
// family is recomputed with independent math/big references, and the sweep
// totals are pinned so that the printed certificate cannot drift silently.

package main

import (
	"math/big"
	"testing"
)

// referenceSum recomputes the geometric sum 1 + q + ... + q^(k-1) by Horner's
// rule, which is a different evaluation order from the repetitive addition of
// RepunitSum.
func referenceSum(q uint64, k int) *big.Int {
	base := new(big.Int).SetUint64(q)
	sum := new(big.Int)
	for j := 0; j < k; j++ {
		sum.Mul(sum, base)
		sum.Add(sum, big.NewInt(1))
	}
	return sum
}

// referenceStep recomputes one instruction with divisor D and unit offset.
func referenceStep(q uint64, D, n *big.Int) *big.Int {
	quot, rem := new(big.Int).QuoRem(n, D, new(big.Int))
	if rem.Sign() == 0 {
		return quot
	}
	out := new(big.Int).Mul(new(big.Int).SetUint64(q), n)
	return out.Add(out, big.NewInt(1))
}

// TestRepunitSumMatchesReference compares the geometric sum with the reference
// over the multiplier range of the sweeps and the degenerate index zero.
func TestRepunitSumMatchesReference(t *testing.T) {
	for q := uint64(2); q <= repunitMaxQ; q++ {
		for k := 0; k <= repunitMaxK; k++ {
			got := RepunitSum(q, k)
			want := referenceSum(q, k)
			if got.Cmp(want) != 0 {
				t.Fatalf("RepunitSum(%d,%d) = %s, want %s", q, k, got, want)
			}
		}
	}
}

// TestStepMatchesReference compares one instruction with the reference on both
// sides of the divisor, including states that are multiples of the divisor and
// states that are not.
func TestStepMatchesReference(t *testing.T) {
	w := NewWorkspace()
	for q := uint64(2); q <= repunitMaxQ; q++ {
		for k := 2; k <= 4; k++ {
			D := RepunitSum(q, k)
			for n := int64(0); n <= 100; n++ {
				w.Cur.SetInt64(n)
				got := new(big.Int).Set(w.StepBig(q, D, w.Cur, w.Next))
				want := referenceStep(q, D, big.NewInt(n))
				if got.Cmp(want) != 0 {
					t.Fatalf("StepBig(q=%d,D=%s,n=%d) = %s, want %s",
						q, D, n, got, want)
				}
			}
		}
	}
	w.Cur.SetString("1208925819614629174706176", 10)
	D := new(big.Int).Exp(big.NewInt(2), big.NewInt(100), nil)
	got := new(big.Int).Set(w.StepBig(3, D, w.Cur, w.Next))
	if want := referenceStep(3, D, w.Cur); got.Cmp(want) != 0 {
		t.Fatalf("wide StepBig = %s, want %s", got, want)
	}
	// The division branch with both operands wider than a word: the state
	// 2^200 is a multiple of the divisor 2^100, and the quotient is 2^100.
	wide := new(big.Int).Lsh(big.NewInt(1), 200)
	w.Cur.Set(wide)
	got = new(big.Int).Set(w.StepBig(3, D, w.Cur, w.Next))
	if want := referenceStep(3, D, w.Cur); got.Cmp(want) != 0 {
		t.Fatalf("wide division StepBig = %s, want %s", got, want)
	}
	if want := new(big.Int).Lsh(big.NewInt(1), 100); got.Cmp(want) != 0 {
		t.Fatalf("wide division quotient = %s, want %s", got, want)
	}
}

// TestOrderMatchesReference recomputes the multiplicative order of q modulo
// the repunit sum by brute force and requires it to be exactly k.
func TestOrderMatchesReference(t *testing.T) {
	for q := uint64(2); q <= 12; q++ {
		for k := 2; k <= 8; k++ {
			D := RepunitSum(q, k)
			pow := big.NewInt(1)
			base := big.NewInt(int64(q))
			order := 0
			for j := 1; j <= k; j++ {
				pow.Mul(pow, base)
				pow.Mod(pow, D)
				if pow.Cmp(big.NewInt(1)) == 0 {
					order = j
					break
				}
			}
			if order != k {
				t.Fatalf("order of %d modulo %s is %d, want %d", q, D, order, k)
			}
		}
	}
}

// TestCycleAndMinimality walks the unit cycle independently: the states after
// j steps are the repunit sums, the return happens at time k and at no earlier
// positive time.
func TestCycleAndMinimality(t *testing.T) {
	one := big.NewInt(1)
	for q := uint64(2); q <= repunitMaxQ; q++ {
		for k := 2; k <= repunitMaxK; k++ {
			D := RepunitSum(q, k)
			cur := big.NewInt(1)
			for j := 1; j <= k; j++ {
				cur = referenceStep(q, D, cur)
				want := referenceSum(q, j+1)
				if j == k {
					want = one
				} else if want.Cmp(one) == 0 {
					t.Fatalf("repunit sum of q=%d index %d is one", q, j+1)
				}
				if cur.Cmp(want) != 0 {
					t.Fatalf("cycle state at q=%d k=%d time %d: %s, want %s",
						q, k, j, cur, want)
				}
				if j < k && cur.Cmp(one) == 0 {
					t.Fatalf("q=%d k=%d returned to 1 at time %d", q, k, j)
				}
			}
		}
	}
}

// TestTrapAndControl checks that zero is the only state sent to zero, that a
// divisor which is not a repunit sum gives no return to one, and that the
// multiplier one breaks the order claim.
func TestTrapAndControl(t *testing.T) {
	w := NewWorkspace()
	D := RepunitSum(2, 7)
	w.Cur.SetUint64(0)
	if got := w.StepBig(2, D, w.Cur, w.Next); got.Sign() != 0 {
		t.Fatalf("zero is not a trap state: %s", got)
	}
	w.Cur.SetUint64(127)
	if got := w.StepBig(2, D, w.Cur, w.Next); got.Sign() == 0 {
		t.Fatalf("a nonzero multiple of the divisor reached zero")
	}
	D = big.NewInt(5)
	cur := big.NewInt(1)
	for j := 1; j <= repunitSteps; j++ {
		cur = referenceStep(2, D, cur)
		if cur.Cmp(big.NewInt(1)) == 0 {
			t.Fatalf("non-repunit divisor returned to 1 at time %d", j)
		}
	}
	for k := 2; k <= repunitMaxK; k++ {
		// The order claim of the slice fails at multiplier one: 1^j is one
		// for every 0 < j < k, so the minimality predicate has no witness.
		D := RepunitSum(1, k)
		if got := new(big.Int).Exp(big.NewInt(1), big.NewInt(int64(k)), D); got.Cmp(big.NewInt(1)) != 0 {
			t.Fatalf("multiplier one failed the power identity at k=%d", k)
		}
		violated := false
		for j := 1; j < k; j++ {
			if got := new(big.Int).Exp(big.NewInt(1), big.NewInt(int64(j)), D); got.Cmp(big.NewInt(1)) == 0 {
				violated = true
			}
		}
		if !violated {
			t.Fatalf("multiplier one did not break the order claim at k=%d", k)
		}
	}
}

// TestSweepPredicatesDiscriminate verifies that the sweep predicates are not
// satisfied by a different parameter: the order of q modulo the repunit sum of
// index k is k, while the same exponent with the divisor of index k-1 leaves a
// different residue, so the modulus of the order slice matters.
func TestSweepPredicatesDiscriminate(t *testing.T) {
	q := uint64(2)
	k := 3
	sum := RepunitSum(q, k)
	got := new(big.Int).Exp(big.NewInt(int64(q)), big.NewInt(int64(k)), sum)
	if got.Cmp(big.NewInt(1)) != 0 {
		t.Fatalf("order predicate failed at q=%d k=%d: %s", q, k, got)
	}
	smaller := RepunitSum(q, k-1)
	got = new(big.Int).Exp(big.NewInt(int64(q)), big.NewInt(int64(k)), smaller)
	if got.Cmp(big.NewInt(1)) == 0 {
		t.Fatalf("the divisor of index %d satisfies the order claim", k-1)
	}
	trap := RepunitSum(q, 7)
	if got := referenceStep(q, trap, big.NewInt(0)); got.Sign() != 0 {
		t.Fatalf("zero did not reach zero: %s", got)
	}
	if got := referenceStep(q, trap, big.NewInt(1)); got.Sign() == 0 {
		t.Fatalf("a nonzero state reached zero")
	}
}

// TestSweepTotals pins every slice count of the certificate and reruns each
// slice, so that a change in the checks is visible as a test failure.
func TestSweepTotals(t *testing.T) {
	want := []uint64{760, 3971, 7581, 12274, 72561, 722}
	slices := []func(uint64, *Workspace, *Totals){
		sweepDivisors,
		sweepOrder,
		sweepCycle,
		sweepResidues,
		sweepTraps,
		sweepReturns,
	}
	var total, repeat Totals
	for i, slice := range slices {
		got := runParallel(slice)
		if got.Failures != 0 || got.Checks != want[i] {
			t.Fatalf("slice %d counted %+v, want checks %d and no failures",
				i, got, want[i])
		}
		second := runParallel(slice)
		if second.Failures != 0 || second.Checks != got.Checks {
			t.Fatalf("slice %d rerun counted %+v, first run %+v", i, second, got)
		}
		total.Checks += got.Checks
		repeat.Checks += second.Checks
	}
	control := Totals{}
	sweepControls(NewWorkspace(), &control)
	if control.Failures != 0 || control.Checks != 442 {
		t.Fatalf("controls counted %+v, want 442 checks and no failures", control)
	}
	total.Checks += control.Checks
	if total.Checks != 98311 {
		t.Fatalf("certificate total %d, want 98311", total.Checks)
	}
	if repeat.Checks != 97869 {
		t.Fatalf("second run counted %d checks, want 97869", repeat.Checks)
	}
}

// TestWarmedAllocation requires the workspace walk to allocate nothing once its
// buffers have grown to the width of the walk. Every measured step works on
// multi-word states, and the two steps exercise the two branches of the step: a
// state that is not divisible follows the affine branch, and a multiple of the
// divisor follows the division branch.
func TestWarmedAllocation(t *testing.T) {
	w := NewWorkspace()
	divisor := new(big.Int).Lsh(big.NewInt(1), 100)
	divisor.Add(divisor, big.NewInt(1))
	odd := new(big.Int).Lsh(big.NewInt(1), 300)
	odd.Add(odd, big.NewInt(1))
	multiple := new(big.Int).Mul(divisor, odd)
	walk := func() {
		w.StepBig(3, divisor, odd, w.Cur)
		w.StepBig(3, divisor, multiple, w.Next)
	}
	walk()
	if w.Cur.BitLen() <= 64 || w.Next.BitLen() <= 64 {
		t.Fatalf("warmed walk stayed inside a word, widths %d and %d",
			w.Cur.BitLen(), w.Next.BitLen())
	}
	allocs := testing.AllocsPerRun(50, walk)
	if allocs != 0 {
		t.Fatalf("step walk allocated %v values per run", allocs)
	}
}

// TestDocumentedRanges checks the two range claims of the certificate: the
// trap sweep compares states at most 200*q + 1, and the repunit sums of the
// grid exceed a machine word at the largest index, so the wide arithmetic of
// the certificate is exercised.
func TestDocumentedRanges(t *testing.T) {
	maxTrapState := uint64(200)*repunitMaxQ + 1
	if maxTrapState >= 1<<20 {
		t.Fatalf("trap sweep reaches %d, beyond the documented range", maxTrapState)
	}
	if n := RepunitSum(repunitMaxQ, repunitMaxK).BitLen(); n <= 64 {
		t.Fatalf("largest repunit sum has %d bits, so the wide path is untested", n)
	}
}
