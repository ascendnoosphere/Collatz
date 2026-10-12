// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestConstantTruePredicateRejected refuses a predicate that accepts mismatches.
func TestConstantTruePredicateRejected(t *testing.T) {
	if PredicateSeparates(ConstantTrue) {
		t.Fatal("constantly true predicate was accepted")
	}
	if !PredicateSeparates(EqualReports) {
		t.Fatal("exact equality was rejected")
	}
}

// TestTerminalPhase checks the cycle 1 <-> 2 through the time window.
func TestTerminalPhase(t *testing.T) {
	state := int64(1)
	for m := 0; m <= TimeLimit; m++ {
		want := int64(1)
		if m%2 == 1 {
			want = 2
		}
		if state != want {
			t.Fatalf("phase m=%d state=%d", m, state)
		}
		state = Shortcut(state)
	}
}

// TestHandParentTimes checks the remaining-time case, the odd phase, and nonminimality.
func TestHandParentTimes(t *testing.T) {
	if ParentCertifiedTime(0, 1, 0) != 1 {
		t.Fatal("odd phase time")
	}
	if Iterate(2, 1) != 1 || Shortcut(1) != 2 {
		t.Fatal("terminal cycle step")
	}
	if ParentCertifiedTime(2, 0, 0) != 2 {
		t.Fatal("nonminimal time")
	}
	if Iterate(1, 2) != 1 || Iterate(1, 0) != 1 {
		t.Fatal("two times at 1")
	}
	if ParentCertifiedTime(0, 0, 1) != 1 || Iterate(2, 1) != 1 {
		t.Fatal("remaining parent time")
	}
	source := int64(5 * 8)
	if Iterate(source, 3) != 5 {
		t.Fatal("doubling preimage")
	}
	if ParentCertifiedTime(3, 0, 0) != 3 || Iterate(source, 3) != 5 {
		t.Fatal("prefix before a terminal parent")
	}
}

// TestDecoyHiddenByConstantPredicate shows that a false clock passes a constant predicate.
func TestDecoyHiddenByConstantPredicate(t *testing.T) {
	state := Iterate(2, DecoyTime(0, 1, 0))
	if EqualReports(state, 1) {
		t.Fatal("decoy time captured 2")
	}
	if !ConstantTrue(state, 1) {
		t.Fatal("constant predicate rejected the decoy mismatch")
	}
	if !EqualReports(Iterate(2, ParentCertifiedTime(0, 1, 0)), 1) {
		t.Fatal("phase step did not reach 1")
	}
	checks, failures := CheckDecoy(EqualReports)
	if failures == 0 {
		t.Fatal("decoy time reached 1 on every row")
	}
	constantChecks, constantFailures := CheckDecoy(ConstantTrue)
	if constantFailures != 0 {
		t.Fatal("constantly true predicate reported a decoy failure")
	}
	if constantChecks != checks {
		t.Fatal("predicate changed the decoy check count")
	}
}

// TestGridCount ties the certificate to the admissible-row formula.
func TestGridCount(t *testing.T) {
	checks, failures := CheckGrid(EqualReports)
	if failures != 0 {
		t.Fatalf("failures %d", failures)
	}
	if checks != ExpectedChecks() {
		t.Fatalf("check count %d, formula %d", checks, ExpectedChecks())
	}
	if checks == 0 {
		t.Fatal("empty grid")
	}
	if AdmissibleCount() < 9 {
		t.Fatal("parent 1 lost even arrival times")
	}
	constantChecks, constantFailures := CheckGrid(ConstantTrue)
	if constantFailures != 0 {
		t.Fatal("constantly true predicate reported a grid failure")
	}
	if constantChecks != checks {
		t.Fatal("predicate changed the grid check count")
	}
	if PredicateSeparates(ConstantTrue) {
		t.Fatal("zero failures were read as a separating predicate")
	}
}
