// SPDX-License-Identifier: CC-BY-4.0
package main

import "testing"

// TestTailCertificates tests signed odd guards and offset shifts over a declared finite grid.
func TestTailCertificates(t *testing.T) {
	for q := int64(-12); q <= 12; q++ {
		for c := int64(-11); c <= 11; c++ {
			if (q+c)%2 == 0 {
				continue
			}
			for n := int64(-128); n <= 128; n++ {
				if n != 0 {
					if err := VerifyTail(q, c, n, 12); err != nil {
						t.Fatal(err)
					}
				}
			}
		}
	}
}

// TestMersennePhases checks exact raw phases at exponents beyond the machine-word range.
func TestMersennePhases(t *testing.T) {
	for k := uint(0); k <= 256; k++ {
		if err := VerifyMersenne(k); err != nil {
			t.Fatal(err)
		}
	}
}

// TestUnitCapture checks the proved logarithmic raw-clock bound on positive samples.
func TestUnitCapture(t *testing.T) {
	for n := int64(1); n <= 10000; n++ {
		if err := VerifyUnit(n); err != nil {
			t.Fatal(err)
		}
	}
}

// TestGoldenCylinders exhausts every low-digit source and legal word in its finite budgets.
func TestGoldenCylinders(t *testing.T) {
	for q := int64(-7); q <= 7; q += 2 {
		for c := int64(-7); c <= 7; c += 2 {
			for h := uint(0); h <= 12; h++ {
				if err := VerifyGoldenCylinders(q, c, h); err != nil {
					t.Fatal(err)
				}
			}
		}
	}
}

// TestGoldenWordCounts compares explicit words to the Fibonacci and trace recurrences.
func TestGoldenWordCounts(t *testing.T) {
	w0, w1 := 1, 2
	p0, p1 := 2, 1
	for h := uint(1); h <= 16; h++ {
		words, periodic := WordCounts(h)
		if words != w1 || periodic != p1 {
			t.Fatalf("depth %d counts (%d,%d), expected (%d,%d)", h, words, periodic, w1, p1)
		}
		w0, w1 = w1, w0+w1
		p0, p1 = p1, p0+p1
	}
}

// TestInvalidBudgets ensures unsupported guard models cannot silently pass a finite check.
func TestInvalidBudgets(t *testing.T) {
	if VerifyTail(3, 1, 1, 2) == nil {
		t.Fatal("same-parity coefficients accepted for the odd-tail certificate")
	}
	if VerifyUnit(0) == nil {
		t.Fatal("zero accepted as a positive unit-capture seed")
	}
	if VerifyGoldenCylinders(8, 1, 3) == nil {
		t.Fatal("even multiplier accepted as a golden-mean cylinder model")
	}
	if VerifyGoldenCylinders(3, 1, 13) == nil {
		t.Fatal("depth beyond the declared int64 budget accepted")
	}
}
