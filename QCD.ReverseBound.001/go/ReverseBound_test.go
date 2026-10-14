// SPDX-License-Identifier: CC-BY-4.0
package main

import "testing"

// TestUnitBoundary distinguishes the sharp minimum from a falsely strict comparison.
func TestUnitBoundary(t *testing.T) {
	holds, known := ProductStrict(1, 3, 2)
	if !known || holds {
		t.Fatal("the state-1 equality must not be strict")
	}
	holds, known = ProductStrict(2, 3, 2)
	if !known || !holds {
		t.Fatal("minimum 2 must give a strict defect")
	}
	holds, known = SquareBelow(2, 1)
	if !known || holds {
		t.Fatal("the integer root must be outside the strict square window")
	}
	holds, known = CeilingHolds(2, 2, 1)
	if known || holds {
		t.Fatal("the ceiling must reject a multiplier outside its window")
	}
	holds, known = ProductStrict(2, 0, 0)
	if !known || !holds {
		t.Fatal("the algebraic zero-total boundary must retain its strict defect")
	}
}

// TestFactorBoundaries includes equal factors and the zero factor at q=2^m.
func TestFactorBoundaries(t *testing.T) {
	for m := uint64(0); m <= MaxRank; m++ {
		root, _ := PowerTwo(m)
		for _, q := range []uint64{0, root} {
			holds, known := FactorHolds(m, q)
			if !known || !holds {
				t.Fatalf("factor boundary m=%d q=%d", m, q)
			}
		}
		holds, known := RecoverHolds(m, root)
		if !known || !holds {
			t.Fatalf("equal factors did not recover q=0 at m=%d", m)
		}
		if holds, known = RecoverHolds(m, root+1); known || holds {
			t.Fatalf("unordered factor boundary accepted at m=%d", m)
		}
	}
}

// TestDeltaSeven checks the factor and recovery computations at the unique pair.
func TestDeltaSeven(t *testing.T) {
	holds, known := FactorHolds(2, 3)
	if !known || !holds {
		t.Fatal("the factors of 16-9 must satisfy all three identities")
	}
	holds, known = RecoverHolds(2, 1)
	if !known || !holds {
		t.Fatal("the pair 1+7 must recover q=3")
	}
}

// TestLettersAndClosure distinguishes present equations from an absent premise.
func TestLettersAndClosure(t *testing.T) {
	for _, tuple := range [][5]uint64{{3, 1, 1, 2, 2}, {5, 1, 3, 1, 4}, {0, 1, 1, 0, 0}} {
		q, x, y, a, b := tuple[0], tuple[1], tuple[2], tuple[3], tuple[4]
		present, known := LettersHold(q, x, y, a, b)
		if !known || !present {
			t.Fatalf("expected present letters: %v", tuple)
		}
		holds, known := ClosureAgrees(q, x, y, a, b)
		if !known || !holds {
			t.Fatalf("substitution failed: %v", tuple)
		}
	}
	present, known := LettersHold(3, 3, 3, 2, 2)
	if !known || present {
		t.Fatal("false letters were accepted")
	}
	if holds, known := ClosureAgrees(3, 3, 3, 2, 2); known || holds {
		t.Fatal("an absent premise was counted as a verified closure")
	}
}

// TestOverflowControls rejects exponent wraparound and every arithmetic boundary.
func TestOverflowControls(t *testing.T) {
	max := ^uint64(0)
	for _, exponent := range []uint64{64, max} {
		if _, known := PowerTwo(exponent); known {
			t.Fatalf("unrepresentable power accepted: %d", exponent)
		}
	}
	for _, rank := range []uint64{32, 64, uint64(1) << 63, max} {
		if _, known := SquareBelow(0, rank); known {
			t.Fatalf("unrepresentable square exponent accepted: %d", rank)
		}
		if _, known := ProductStrict(2, 0, rank); known {
			t.Fatalf("unrepresentable product exponent accepted: %d", rank)
		}
		if _, known := FactorHolds(rank, 0); known {
			t.Fatalf("unrepresentable factor rank accepted: %d", rank)
		}
		if _, known := RecoverHolds(rank, 0); known {
			t.Fatalf("unrepresentable recovery rank accepted: %d", rank)
		}
	}
	if _, known := MultiplyChecked(max, 2); known {
		t.Fatal("overflowed product accepted")
	}
	if product, known := MultiplyChecked(max, 1); !known || product != max {
		t.Fatal("representable product rejected")
	}
	if product, known := MultiplyChecked(max, 0); !known || product != 0 {
		t.Fatal("zero product rejected")
	}
	if _, known := AddChecked(max, 1); known {
		t.Fatal("overflowed sum accepted")
	}
	if _, known := SubtractChecked(0, 1); known {
		t.Fatal("negative difference accepted")
	}
	if _, known := SquareBelow(max, 1); known {
		t.Fatal("overflowed multiplier square accepted")
	}
	if _, known := ProductStrict(max, 0, 0); known {
		t.Fatal("overflowed minimum square accepted")
	}
	if _, known := LettersHold(max, 2, 2, 1, 1); known {
		t.Fatal("overflowed letter product accepted")
	}
	if _, known := ClosureAgrees(0, 1, 1, max, 1); known {
		t.Fatal("overflowed clock accepted")
	}
	if _, known := SlackHolds(2, max, 2); known {
		t.Fatal("overflowed slack accepted")
	}
}

// TestSlack checks both equality at the minimum and rejection below it.
func TestSlack(t *testing.T) {
	holds, known := SlackHolds(2, 3, 2)
	if !known || !holds {
		t.Fatal("zero slack was not restored exactly")
	}
	if holds, known = SlackHolds(3, 3, 2); known || holds {
		t.Fatal("a state below the minimum was accepted")
	}
}

// TestScanRankAllocations keeps the numerical rank worker allocation-free.
func TestScanRankAllocations(t *testing.T) {
	allocations := testing.AllocsPerRun(10, func() { ScanRank(4) })
	if allocations != 0 {
		t.Fatalf("rank worker allocations=%g", allocations)
	}
	for _, rank := range []uint64{0, MaxRank + 1, ^uint64(0)} {
		checks, failures, _ := ScanRank(rank)
		if checks != 0 || failures != 1 {
			t.Fatalf("unsupported rank was not rejected: %d", rank)
		}
	}
}

// TestScan requires every grid comparison and the unique difference-seven hit.
func TestScan(t *testing.T) {
	checks, failures, sevenHits := Scan()
	if checks <= 0 || failures != 0 || sevenHits != 1 {
		t.Fatalf("checks=%d failures=%d seven hits=%d", checks, failures, sevenHits)
	}
}
