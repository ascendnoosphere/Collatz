// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestAllWords checks the complete supported family, including the empty word.
func TestAllWords(t *testing.T) {
	for h := uint(0); h <= MaxHalf; h++ {
		r := ScanHalf(h)
		if r.Err != nil || r.Checked != uint64(1)<<(2*h) {
			t.Fatalf("half-length %d: %+v", h, r)
		}
	}
}

// TestExamples distinguishes sharpness and each of the three necessary hypotheses.
func TestExamples(t *testing.T) {
	cases := []struct {
		word     Word
		count    uint
		distance uint
		cut      uint
		balanced bool
	}{
		{Word{368, 12}, 4, 4, 0, true}, // 000011101000: sharp gap.
		{Word{1, 2}, 1, 1, 0, false},   // 10: the total count is not even.
		{Word{10, 4}, 2, 0, 0, true},   // 0101: a repeated block.
		{Word{12, 4}, 2, 2, 1, true},   // 0011: a transport exists.
		{Word{12, 6}, 2, 2, 0, true},   // 001100: nonadjacent moved positions.
		{Word{192, 8}, 2, 2, 3, true},  // 00000011: the search needs three updates.
	}
	for _, c := range cases {
		count, ok := OddCount(c.word)
		distance, valid := Antipodal(c.word)
		cut, balanced := BalancedCut(c.word)
		if !ok || !valid || count != c.count || distance != c.distance ||
			cut != c.cut || balanced != c.balanced {
			t.Fatalf("example %+v: count=%d distance=%d cut=%d balanced=%v",
				c.word, count, distance, cut, balanced)
		}
		if err := VerifyWord(c.word); err != nil {
			t.Fatal(err)
		}
	}
}

// TestFirstBalancedCut compares the window search against an independent rotation scan.
func TestFirstBalancedCut(t *testing.T) {
	for h := uint(0); h <= 7; h++ {
		for mask := uint64(0); mask < uint64(1)<<(2*h); mask++ {
			w := Word{mask, 2 * h}
			cut, found := BalancedCut(w)
			for k := uint(0); k <= h; k++ {
				r, _ := Rotate(w, k)
				left := r.Bits & LowMask(h)
				right := r.Bits >> h
				u, _ := OddCount(Word{left | left<<h, 2 * h})
				v, _ := OddCount(Word{right | right<<h, 2 * h})
				if u == v {
					if !found || cut != k {
						t.Fatalf("word %+v: first balanced cut %d, returned %d", w, k, cut)
					}
					break
				}
				if k == h && found {
					t.Fatalf("word %+v: returned a nonexistent balanced cut", w)
				}
			}
		}
	}
}

// TestSeparatedTransport checks that the two balanced cuts have nonadjacent mismatches.
func TestSeparatedTransport(t *testing.T) {
	w := Word{12, 6}
	balanced := 0
	for k := uint(0); k < w.Length; k++ {
		r, _ := Rotate(w, k)
		left, right := r.Bits&7, r.Bits>>3
		if (left == 1 && right == 4) || (left == 4 && right == 1) {
			balanced++
			if left^right != 5 {
				t.Fatal("moved positions are not the first and third")
			}
		} else if left != 0 && right != 0 {
			t.Fatal("unexpected balanced cut")
		}
	}
	if balanced != 2 {
		t.Fatalf("balanced cuts: %d", balanced)
	}
}

// TestBudgets rejects malformed inputs before shifts, allocations or exhaustive work.
func TestBudgets(t *testing.T) {
	invalid := []Word{{1, 0}, {1, 1}, {1 << 20, 20}, {0, 22}, {0, ^uint(0)}}
	for _, w := range invalid {
		if ValidWord(w) || VerifyWord(w) == nil {
			t.Fatalf("invalid word accepted: %+v", w)
		}
		if _, ok := Rotate(w, ^uint(0)); ok {
			t.Fatal("rotation accepted an invalid word")
		}
		if _, ok := BalancedCut(w); ok {
			t.Fatal("balanced-cut search accepted an invalid word")
		}
		if _, ok := OddCount(w); ok {
			t.Fatal("count accepted an invalid word")
		}
		if _, ok := Antipodal(w); ok {
			t.Fatal("distance accepted an invalid word")
		}
	}
	for _, h := range []uint{MaxHalf + 1, ^uint(0)} {
		if r := ScanHalf(h); r.Err == nil || r.Checked != 0 {
			t.Fatalf("invalid half-length accepted: %d", h)
		}
	}
	if !ValidWord(Word{LowMask(MaxLength), MaxLength}) {
		t.Fatal("largest supported mask rejected")
	}
}

// TestRotationBoundaries handles empty words and very large rotation indices exactly.
func TestRotationBoundaries(t *testing.T) {
	if r, ok := Rotate(Word{}, ^uint(0)); !ok || r != (Word{}) {
		t.Fatal("empty-word rotation failed")
	}
	w := Word{12, 6}
	r, ok := Rotate(w, ^uint(0))
	expected, _ := Rotate(w, ^uint(0)%w.Length)
	if !ok || r != expected {
		t.Fatal("large rotation was not reduced modulo length")
	}
	if LowMask(0) != 0 || LowMask(64) != ^uint64(0) ||
		LowMask(^uint(0)) != ^uint64(0) {
		t.Fatal("mask saturation failed")
	}
}

// TestCheckAllocations requires reusable scalar checks to allocate nothing on success.
func TestCheckAllocations(t *testing.T) {
	w := Word{368, 12}
	allocs := testing.AllocsPerRun(100, func() {
		if err := VerifyWord(w); err != nil {
			t.Fatal(err)
		}
	})
	if allocs != 0 {
		t.Fatalf("allocations per check: %g", allocs)
	}
}
