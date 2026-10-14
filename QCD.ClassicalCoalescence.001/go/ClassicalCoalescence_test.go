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

// TestPairedTailWords checks all six proved ranks and includes the empty parent run.
func TestPairedTailWords(t *testing.T) {
	for _, expected := range [6]struct {
		drop, a, checked, removed, multiples int
	}{
		{3, 4, 31, 18, 11}, {3, 5, 16, 8, 6}, {3, 6, 8, 4, 2},
		{2, 2, 246, 133, 84}, {2, 3, 123, 66, 39}, {2, 4, 60, 32, 21},
	} {
		checked, removed, multiples, err := VerifyPairedTails(expected.drop, expected.a, 1000000)
		if err != nil {
			t.Fatal(err)
		}
		if checked != expected.checked || removed != expected.removed ||
			multiples != expected.multiples {
			t.Fatalf("changed paired coverage drop=%d a=%d: %d %d %d",
				expected.drop, expected.a, checked, removed, multiples)
		}
		// The successful finite verifier should not allocate inside any source loop.
		allocations := testing.AllocsPerRun(1, func() {
			if _, _, _, err := VerifyPairedTails(expected.drop, expected.a, 1000000); err != nil {
				t.Fatal(err)
			}
		})
		if allocations != 0 {
			t.Fatalf("paired verifier allocated: %g", allocations)
		}
	}
	if err := VerifyTailCylinders(10000); err != nil {
		t.Fatal(err)
	}
	for _, limit := range []int{-1, 10001} {
		if err := VerifyTailCylinders(limit); err == nil {
			t.Fatalf("accepted unsupported cylinder budget: %d", limit)
		}
	}
	for _, limit := range []uint64{0, 62, 1000001} {
		if _, _, _, err := VerifyPairedTails(3, 4, limit); err == nil {
			t.Fatalf("accepted unsupported paired budget: %d", limit)
		}
	}
	for _, family := range [6]struct{ drop, a int }{
		{1, 2}, {3, 3}, {3, 7}, {2, 1}, {2, 5}, {4, 6},
	} {
		if _, _, _, err := VerifyPairedTails(family.drop, family.a, 1000000); err == nil {
			t.Fatalf("accepted unsupported paired rank: %+v", family)
		}
	}
}

// TestTailCoefficients independently compares every finite input with final integrality.
func TestTailCoefficients(t *testing.T) {
	for _, tail := range [3]struct{ mask, p, b uint64 }{
		{128, 3, 128}, {130, 9, 134}, {58, 81, 206},
	} {
		p, q, b := WordData(tail.mask, 8)
		if p != int64(tail.p) || q != 256 || b != int64(tail.b) || b-p != 125 {
			t.Fatalf("wrong centered tail coefficients: %+v", tail)
		}
		for x := uint64(0); x < 65536; x++ {
			if LegalRepeated(tail.mask, 8, x, 1) != ((tail.p*x+tail.b)%256 == 0) {
				t.Fatalf("tail integrality mismatch: mask=%d x=%d", tail.mask, x)
			}
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
