// SPDX-License-Identifier: CC-BY-4.0

package main

import "testing"

// TestAcceleratedEdge checks the two-letter edge at 5.
func TestAcceleratedEdge(t *testing.T) {
	var word [WordCap]byte
	word[0] = LetterAffine
	word[1] = LetterDivision
	end, legal := Replay(&word, 2, 5, 3, 1, 2)
	if !legal || end != 8 {
		t.Fatalf("Replay = %d, legal %t", end, legal)
	}
	p, ok := Solve(&word, 2, 8, 3, 1, 2)
	if !ok || p != 5 {
		t.Fatalf("Solve = %d, ok %t", p, ok)
	}
}

// TestThreeReplays checks the three legal ascending words ending at 8.
func TestThreeReplays(t *testing.T) {
	var two [WordCap]byte
	two[0] = LetterAffine
	two[1] = LetterDivision
	two[2] = LetterAffine
	two[3] = LetterDivision
	p, ok := Solve(&two, 4, 8, 3, 1, 2)
	if !ok || p != 3 {
		t.Fatalf("two edges Solve = %d, ok %t", p, ok)
	}
	var three [WordCap]byte
	three[0] = LetterDivision
	three[1] = LetterAffine
	three[2] = LetterDivision
	three[3] = LetterAffine
	three[4] = LetterDivision
	p, ok = Solve(&three, 5, 8, 3, 1, 2)
	if !ok || p != 6 {
		t.Fatalf("tower Solve = %d, ok %t", p, ok)
	}
}

// TestSmallTree compares inverse enumeration with every smaller positive seed.
func TestSmallTree(t *testing.T) {
	nodes, paths, ok := CountInverse(8, 3, 1, 2, 3)
	if !ok {
		t.Fatal("inverse count overflowed or was truncated")
	}
	if nodes != 3 || paths != 3 {
		t.Fatalf("inverse nodes=%d paths=%d", nodes, paths)
	}
	fwd, fok := CountForward(8, 3, 1, 2, 3)
	if !fok || fwd != 3 {
		t.Fatalf("forward nodes=%d ok=%t", fwd, fok)
	}
}

// TestBudgetNumbers checks the boundary 2^5 < 4^3 and 2^6 = 4^3.
func TestBudgetNumbers(t *testing.T) {
	holds, known := BelowBudget(2, 4, 5, 3)
	if !known || !holds {
		t.Fatal("expected 2^5 < 4^3")
	}
	holds, known = BelowBudget(2, 4, 6, 3)
	if !known || holds {
		t.Fatal("did not expect 2^6 < 4^3")
	}
	left, lok := PowIter(2, 5)
	right, rok := PowIter(4, 3)
	if !lok || !rok || left != 32 || right != 64 || !(5 < right) {
		t.Fatalf("powers %d %d", left, right)
	}
}

// TestImplicationGrid checks the exponent consequence on a bounded rectangle.
func TestImplicationGrid(t *testing.T) {
	fails, ok := ImplicationFailures(8, 12)
	if !ok {
		t.Fatal("the two power algorithms disagreed")
	}
	if fails != 0 {
		t.Fatalf("implication failures=%d", fails)
	}
	if MonotoneFailures(8, 12) != 0 {
		t.Fatal("a power decreased")
	}
}

// TestNecessityGrid checks ascending hits inside one bounded rectangle.
func TestNecessityGrid(t *testing.T) {
	fails, ok := NecessityFailures(4, 4, 4, 12, 3)
	if !ok {
		t.Fatal("the bounded orbit walk did not finish")
	}
	if fails != 0 {
		t.Fatalf("necessity failures=%d", fails)
	}
}

// TestDivisionTowerStaysAbove checks a pure division preimage is not ascending.
func TestDivisionTowerStaysAbove(t *testing.T) {
	var word [WordCap]byte
	word[0] = LetterDivision
	end, legal := Replay(&word, 1, 16, 3, 1, 2)
	if !legal || end != 8 {
		t.Fatalf("division Replay = %d, legal %t", end, legal)
	}
	holds, known := BelowBudget(2, 4, 1, 0)
	if !known || holds {
		t.Fatal("a pure division was placed inside the budget")
	}
}

// TestWordCounts covers all binary words through the supported length.
func TestWordCounts(t *testing.T) {
	if err := VerifyWordCounts(WordCap); err != nil {
		t.Fatal(err)
	}
	for _, h := range []int{-1, WordCap + 1} {
		if err := VerifyWordCounts(h); err == nil {
			t.Fatalf("accepted word length %d", h)
		}
	}
}

// TestInverseForwardGrid checks every start, not just the necessary inequality.
func TestInverseForwardGrid(t *testing.T) {
	for D := uint64(2); D <= 4; D++ {
		for q := uint64(1); q <= 4; q++ {
			for c := uint64(1); c <= 4; c++ {
				for m := uint64(2); m <= 12; m++ {
					for s := 1; s <= 3; s++ {
						n, _, ok := CountInverse(m, q, c, D, s)
						f, fok := CountForward(m, q, c, D, s)
						if !ok || !fok || n != f {
							t.Fatalf("D=%d q=%d c=%d m=%d s=%d: inverse %d/%t forward %d/%t",
								D, q, c, m, s, n, ok, f, fok)
						}
					}
				}
			}
		}
	}
}

// TestInvalidInputs rejects malformed words before indexing or replaying them.
func TestInvalidInputs(t *testing.T) {
	var word [WordCap]byte
	for _, n := range []int{-1, 0, WordCap + 1} {
		if _, ok := Solve(&word, n, 8, 3, 1, 2); ok {
			t.Fatalf("accepted solve length %d", n)
		}
	}
	for _, n := range []int{-1, WordCap + 1} {
		if _, ok := Replay(&word, n, 1, 3, 1, 2); ok {
			t.Fatalf("accepted replay length %d", n)
		}
	}
	word[0] = 2
	if _, ok := Replay(&word, 1, 8, 3, 1, 2); ok {
		t.Fatal("accepted invalid replay letter")
	}
	if _, ok := OffsetOf(&word, 1, 3, 2); ok {
		t.Fatal("accepted invalid offset letter")
	}
	if _, ok := Solve(&word, 1, 8, 3, 1, 2); ok {
		t.Fatal("accepted invalid solve letter")
	}
	if _, ok := Replay(nil, 0, 1, 3, 1, 2); ok {
		t.Fatal("accepted nil word")
	}
	for _, s := range []int{0, WordCap + 1} {
		if _, _, ok := CountInverse(8, 3, 1, 2, s); ok {
			t.Fatalf("accepted affine ceiling %d", s)
		}
	}
}

// TestVerifierBudgets prevents wrapping loop counters on unsupported grids.
func TestVerifierBudgets(t *testing.T) {
	if _, ok := ImplicationFailures(33, 12); ok {
		t.Fatal("accepted unsupported power grid")
	}
	if _, ok := ImplicationFailures(8, 65); ok {
		t.Fatal("accepted unsupported exponent grid")
	}
	if MonotoneFailures(33, 12) != -1 {
		t.Fatal("accepted unsupported monotonicity grid")
	}
	if _, ok := NecessityFailures(9, 4, 4, 12, 3); ok {
		t.Fatal("accepted unsupported orbit grid")
	}
	if _, ok := CountForward(1, 0, 1, 2, 1); ok {
		t.Fatal("accepted invalid parameters at an empty forward range")
	}
}

// TestOverflow keeps unknown arithmetic distinct from a false inequality.
func TestOverflow(t *testing.T) {
	max := ^uint64(0)
	if _, ok := AddOK(max, 1); ok {
		t.Fatal("addition overflow was accepted")
	}
	if _, ok := MulOK(max, 2); ok {
		t.Fatal("multiplication overflow was accepted")
	}
	if _, known := BelowBudget(2, 2, 64, 1); known {
		t.Fatal("overflowing power was treated as known")
	}
	if _, _, ok := CountInverse(8, max, 1, 2, 1); ok {
		t.Fatal("overflowing q+c was accepted")
	}
	for _, base := range []uint64{0, 1, 2} {
		a, ok := PowIter(base, max)
		b, bok := PowSquare(base, max)
		if ok != bok || (ok && a != b) {
			t.Fatalf("power disagreement for base %d", base)
		}
	}
}

// TestSearchAllocations keeps the supported inverse walk in stack storage.
func TestSearchAllocations(t *testing.T) {
	if n := testing.AllocsPerRun(100, func() {
		CountInverse(8, 3, 1, 2, 3)
	}); n != 0 {
		t.Fatalf("inverse search allocated %.0f objects", n)
	}
}
