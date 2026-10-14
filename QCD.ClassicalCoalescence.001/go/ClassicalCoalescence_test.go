// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestParentFamilies checks all displayed guards and the reduced residual membership.
func TestParentFamilies(t *testing.T) {
	if err := VerifyFamilies(10000); err != nil {
		t.Fatal(err)
	}
	if err := VerifyResidualRules(100000); err != nil {
		t.Fatal(err)
	}
}

// TestExactBudgets compares word legality with signed displacement divisibility.
func TestExactBudgets(t *testing.T) {
	count, err := VerifyBudgets()
	if err != nil {
		t.Fatal(err)
	}
	if count != 522240 {
		t.Fatalf("unexpected repeated-word coverage: %d", count)
	}
}

// TestCrossingGap checks the three-crossing extension, including exterior support slots.
func TestCrossingGap(t *testing.T) {
	if _, err := VerifyCrossings(); err != nil {
		t.Fatal(err)
	}
}

// TestFiveCompositions checks that the finite reduction covers exactly 35 ordered words.
func TestFiveCompositions(t *testing.T) {
	count, err := VerifyFiveCompositions()
	if err != nil {
		t.Fatal(err)
	}
	if count != 35 {
		t.Fatalf("unexpected five-return coverage: %d", count)
	}
}

// TestTerminalClocks uses exact integers beyond machine-word size for all nine cases.
func TestTerminalClocks(t *testing.T) {
	if err := VerifyTerminal(); err != nil {
		t.Fatal(err)
	}
}
