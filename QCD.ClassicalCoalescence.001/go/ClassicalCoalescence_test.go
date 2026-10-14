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

// TestSecondBurstWords includes both initial lengths and the empty parent odd run.
func TestSecondBurstWords(t *testing.T) {
	for _, expected := range [2]struct {
		a, checked, removed, multiples int
	}{
		{2, 31250, 8487, 5208},
		{3, 15625, 8487, 5212},
	} {
		checked, removed, multiples, err := VerifySecondBursts(expected.a, 1000000)
		if err != nil {
			t.Fatal(err)
		}
		if checked != expected.checked || removed != expected.removed ||
			multiples != expected.multiples {
			t.Fatalf("changed second-burst coverage a=%d: %d %d %d",
				expected.a, checked, removed, multiples)
		}
	}
	for _, limit := range []uint64{0, 6, 1000001} {
		if _, _, _, err := VerifySecondBursts(2, limit); err == nil {
			t.Fatalf("accepted unsupported budget: %d", limit)
		}
	}
	for _, a := range []int{1, 4} {
		if _, _, _, err := VerifySecondBursts(a, 1000000); err == nil {
			t.Fatalf("accepted unsupported initial burst: %d", a)
		}
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
