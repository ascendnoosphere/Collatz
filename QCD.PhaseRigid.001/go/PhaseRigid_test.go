// SPDX-License-Identifier: CC-BY-4.0
//
// Tests for the divided-branch congruence. The parity grid is recomputed by
// an independent loop, cells outside the odd hypothesis reject a constantly
// true predicate, and the length-16 defect is pinned to 4858/6487.

package main

import (
	"math/big"
	"testing"
)

// TestParityGridMatchesIndependentLoop recomputes the parity check count.
func TestParityGridMatchesIndependentLoop(t *testing.T) {
	got := sweepParity()
	if got.Failures != 0 {
		t.Fatalf("parity failures %d", got.Failures)
	}
	var want uint64
	for q := uint64(1); q <= phaseRigidMaxQ; q += 2 {
		for c := uint64(1); c <= phaseRigidMaxQ; c += 2 {
			for n := uint64(0); n <= phaseRigidMaxN; n++ {
				if n%2 == 1 {
					if !phaseRigidOddNumeratorEven(q, c, n) ||
						!phaseRigidOddBranchExact(q, c, n) {
						t.Fatalf("odd cell q=%d c=%d n=%d", q, c, n)
					}
					want += 2
				} else {
					if !phaseRigidEvenHalves(n) {
						t.Fatalf("even cell n=%d", n)
					}
					want++
				}
			}
		}
	}
	if got.Checks != want {
		t.Fatalf("parity checks %d, independent count %d", got.Checks, want)
	}
}

// TestConstantTruePredicateRejected fails if the congruence ignores its inputs.
func TestConstantTruePredicateRejected(t *testing.T) {
	always := func(q, c, n uint64) bool { return true }
	if phaseRigidOddNumeratorEven(3, 2, 1) {
		t.Fatal("even offset satisfied the odd congruence")
	}
	if always(3, 2, 1) == phaseRigidOddNumeratorEven(3, 2, 1) {
		t.Fatal("odd congruence agreed with a constantly true predicate")
	}
	if phaseRigidOddNumeratorEven(3, 1, 2) {
		t.Fatal("even seed satisfied the odd congruence")
	}
	if phaseRigidEvenHalves(1) {
		t.Fatal("odd integer satisfied the even halving identity")
	}
	if !phaseRigidOddNumeratorEven(3, 1, 1) || !phaseRigidOddBranchExact(3, 1, 1) {
		t.Fatal("legal odd cell failed")
	}
}

// TestShortWords pins the defects of the words 10 and 100.
func TestShortWords(t *testing.T) {
	var tot Totals
	num, den := PhaseRigidAudit(3, 1, []bool{true, false}, &tot)
	if tot.Failures != 0 {
		t.Fatalf("word 10 failures %d", tot.Failures)
	}
	if num == nil || num.Sign() != 0 || den.Cmp(big.NewInt(1)) != 0 {
		t.Fatalf("word 10 defect %s/%s", num, den)
	}
	tot = Totals{}
	num, den = PhaseRigidAudit(3, 1, []bool{true, false, false}, &tot)
	if tot.Failures != 0 {
		t.Fatalf("word 100 failures %d", tot.Failures)
	}
	if num == nil || num.Cmp(big.NewInt(8)) != 0 || den.Cmp(big.NewInt(5)) != 0 {
		t.Fatalf("word 100 defect %s/%s, want 8/5", num, den)
	}
	if num.Sign() == 0 {
		t.Fatal("word 100 agreed with a constantly zero defect")
	}
}

// TestWitnessBelowThreeQuarters pins 4858/6487 and rejects the bound 3/4.
func TestWitnessBelowThreeQuarters(t *testing.T) {
	var tot Totals
	num, den := PhaseRigidAudit(3, 1, witnessBits(), &tot)
	if tot.Failures != 0 {
		t.Fatalf("witness failures %d", tot.Failures)
	}
	if num == nil || den == nil ||
		num.Cmp(big.NewInt(4858)) != 0 || den.Cmp(big.NewInt(6487)) != 0 {
		t.Fatalf("witness defect %s/%s, want 4858/6487", num, den)
	}
	if new(big.Int).Mul(big.NewInt(4), num).Cmp(
		new(big.Int).Mul(big.NewInt(3), den)) >= 0 {
		t.Fatal("witness is not strictly below 3/4")
	}
	if new(big.Int).Mul(big.NewInt(5), num).Cmp(new(big.Int).Lsh(den, 1)) < 0 {
		t.Fatal("witness is below 2/5")
	}
	atLeastThreeQuarters := func(n, d *big.Int) bool {
		return new(big.Int).Mul(big.NewInt(4), n).Cmp(
			new(big.Int).Mul(big.NewInt(3), d)) >= 0
	}
	if atLeastThreeQuarters(num, den) {
		t.Fatal("a constantly large-gap predicate accepted the witness")
	}
}

// TestNoncontractingWordIsOutside skips a word with nonpositive determinant.
func TestNoncontractingWordIsOutside(t *testing.T) {
	var tot Totals
	num, den := PhaseRigidAudit(5, 1, []bool{true, true}, &tot)
	if num != nil || den != nil {
		t.Fatal("noncontracting word returned a defect")
	}
	if tot.Checks != 0 || tot.Failures != 0 {
		t.Fatalf("noncontracting word recorded checks %d failures %d",
			tot.Checks, tot.Failures)
	}
}

// TestSweepClean runs the full grid and requires every check to pass.
func TestSweepClean(t *testing.T) {
	total := PhaseRigidSweep()
	if total.Failures != 0 {
		t.Fatalf("failures %d among %d checks", total.Failures, total.Checks)
	}
	if total.Checks == 0 {
		t.Fatal("sweep recorded no checks")
	}
}
