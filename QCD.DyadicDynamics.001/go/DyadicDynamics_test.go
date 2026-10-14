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

// TestGoldenStatistics checks both initial laws and exact stationary moments at every depth.
func TestGoldenStatistics(t *testing.T) {
	for h := uint(1); h <= 16; h++ {
		if err := VerifyGoldenStatistics(h); err != nil {
			t.Fatal(err)
		}
	}
}

// TestReflectionCapture checks the integer example separating finite laws from tail frequency.
func TestReflectionCapture(t *testing.T) {
	for seed := int64(-1000); seed <= 1000; seed++ {
		n, magnitude := seed, seed
		if magnitude < 0 {
			magnitude = -magnitude
		}
		// The first-division descent costs at most two raw ticks per magnitude decrease.
		for tick := int64(0); tick < 2*magnitude+2 && n != 0; tick++ {
			if n%2 == 0 {
				n /= 2
			} else {
				n = 1 - n
			}
		}
		if n != 0 {
			t.Fatalf("reflection seed %d did not reach zero within the descent bound", seed)
		}
	}
}

// TestBoundedBinomial exercises the empty word, symmetry, and the count's integer budget.
func TestBoundedBinomial(t *testing.T) {
	cases := []struct {
		n, k, want int64
	}{
		{0, 0, 1},
		{17, 0, 1},
		{17, 8, 24310},
		{17, 9, 24310},
		{17, 17, 1},
		{5, -1, 0},
		{5, 6, 0},
		{-1, 0, 0},
		{18, 0, 0},
	}
	for _, sample := range cases {
		if got := BoundedBinomial(sample.n, sample.k); got != sample.want {
			t.Errorf("binomial(%d,%d) = %d, want %d", sample.n, sample.k, got, sample.want)
		}
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
	for _, h := range []uint{0, 17} {
		if VerifyGoldenStatistics(h) == nil {
			t.Errorf("statistics accepted unsupported depth %d", h)
		}
	}
}
