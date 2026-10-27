// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestRepeatedWords includes empty words, zero seeds, zero copies, and negative defects.
func TestRepeatedWords(t *testing.T) {
	checks, err := CheckRepeatedWords()
	if err != nil {
		t.Fatal(err)
	}
	if checks != 163200 {
		t.Fatalf("checked %d cases, want 163200", checks)
	}
}

// TestDirectCylinders checks all 31 published direct certificates without parameter sampling.
func TestDirectCylinders(t *testing.T) {
	cases := []struct {
		source, modulus, target, slope uint64
		word                           string
	}{
		{175, 256, 167, 243, "11110100"},
		{199, 256, 190, 243, "11101010"},
		{287, 1024, 205, 729, "1111101000"},
		{367, 1024, 262, 729, "1111011000"},
		{507, 1024, 362, 729, "1101101100"},
		{583, 1024, 416, 729, "1110101100"},
		{815, 1024, 581, 729, "1111010100"},
		{123, 256, 118, 243, "11011010"},
		{347, 1024, 248, 729, "1101110100"},
		{423, 1024, 302, 729, "1110110100"},
		{2203, 4096, 1177, 2187, "110111101000"},
		{3675, 4096, 1963, 2187, "110111011000"},
		{2907, 4096, 1553, 2187, "110111010100"},
		{1787, 4096, 955, 2187, "110110111000"},
		{1019, 4096, 545, 2187, "110110110100"},
		{3143, 4096, 1679, 2187, "111010110100"},
		{3911, 4096, 2089, 2187, "111010111000"},
		{1703, 4096, 910, 2187, "111011011000"},
		{935, 4096, 500, 2187, "111011010100"},
		{231, 4096, 124, 2187, "111011101000"},
		{3119, 4096, 1666, 2187, "111101011000"},
		{2351, 4096, 1256, 2187, "111101010100"},
		{1647, 4096, 880, 2187, "111101101000"},
		{879, 4096, 470, 2187, "111101100100"},
		{2031, 4096, 1085, 2187, "111101110000"},
		{2591, 4096, 1384, 2187, "111110101000"},
		{1823, 4096, 974, 2187, "111110100100"},
		{2975, 4096, 1589, 2187, "111110110000"},
		{2239, 4096, 1196, 2187, "111111010000"},
		{2075, 8192, 1663, 6561, "1101111101000"},
		{27, 1 << 59, 23, 450283905890997363,
			"11011111010110111011110100111011011111100111100010101000100"},
	}
	for _, c := range cases {
		if err := CheckDirectCylinder(c.source, c.modulus, c.target, c.slope, c.word); err != nil {
			t.Fatalf("source=%d: %v", c.source, err)
		}
	}
}

// TestCylinderControls rejects corrupted coefficients, guards, syntax, and expansion.
func TestCylinderControls(t *testing.T) {
	cases := []struct {
		source, modulus, target, slope uint64
		word                           string
	}{
		{175, 256, 168, 243, "11110100"},
		{175, 256, 167, 244, "11110100"},
		{175, 256, 167, 243, "11110101"},
		{177, 256, 167, 243, "11110100"},
		{175, 128, 167, 243, "11110100"},
		{1, 1, 1, 1, "10"},
		{0, 2, 1, 1, "0"},
		{2, 0, 1, 1, "0"},
		{2, 2, 0, 1, "0"},
		{2, 2, 1, 1, ""},
		{2, 2, 1, 1, "x"},
	}
	for _, c := range cases {
		if err := CheckCylinder(c.source, c.modulus, c.target, c.slope, c.word); err == nil {
			t.Fatalf("accepted corrupt certificate: %+v", c)
		}
	}
	if err := CheckCylinder(3, 8, 4, 9, "110"); err != nil {
		t.Fatal(err)
	}
	if err := CheckDirectCylinder(3, 8, 4, 9, "110"); err == nil {
		t.Fatal("accepted expanding identity as a descent")
	}
	if err := CheckDirectCylinder(175, 512, 167, 486, "11110100"); err != nil {
		t.Fatalf("valid thin subcylinder: %v", err)
	}
	// The intermediate odd image exceeds uint64; exact arithmetic must still accept it.
	if err := CheckCylinder(1<<63+1, 4, 6917529027641081857, 3, "10"); err != nil {
		t.Fatalf("large exact cylinder: %v", err)
	}
}

// TestJoinCylinder checks both affine legs and the smaller-parent coefficient comparison.
func TestJoinCylinder(t *testing.T) {
	const sourceModulus, parentModulus = uint64(1<<15) * 2187, uint64(1 << 26)
	const slope = uint64(1<<14) * 6561
	if err := CheckCylinder(111, sourceModulus, 167, slope, "1"); err != nil {
		t.Fatal(err)
	}
	if err := CheckCylinder(103, parentModulus, 167, slope, "111011110100"); err != nil {
		t.Fatal(err)
	}
	if parentModulus >= sourceModulus {
		t.Fatal("join parent slope does not strictly decrease")
	}
}

// TestCycleWindow checks the composition counts as well as the absence of candidates.
func TestCycleWindow(t *testing.T) {
	cases := []struct {
		rank, total, words int
	}{
		{6, 10, 126},
		{7, 12, 462},
		{8, 13, 792},
		{9, 15, 3003},
	}
	for _, c := range cases {
		words, hits, err := CountCycleWords(c.rank, c.total)
		if err != nil {
			t.Fatal(err)
		}
		if words != c.words || hits != 0 {
			t.Fatalf("rank=%d: words=%d hits=%d; want words=%d hits=0",
				c.rank, words, hits, c.words)
		}
	}
	if err := CheckCycleWindow(); err != nil {
		t.Fatal(err)
	}
}

// TestCyclePositiveControl ensures the repeated unit cycle is accepted outside the window.
func TestCyclePositiveControl(t *testing.T) {
	words, hits, err := CountCycleWords(6, 12)
	if err != nil {
		t.Fatal(err)
	}
	if words != 462 || hits != 1 {
		t.Fatalf("words=%d hits=%d, want words=462 hits=1", words, hits)
	}
}

// TestCycleInputBounds rejects unsupported ranks, totals, and nonpositive denominators.
func TestCycleInputBounds(t *testing.T) {
	for _, c := range [][2]int{{5, 10}, {10, 16}, {6, 5}, {6, 13}, {6, 6}} {
		if _, _, err := CountCycleWords(c[0], c[1]); err == nil {
			t.Fatalf("accepted rank=%d total=%d", c[0], c[1])
		}
	}
}
