// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"strconv"
	"testing"
)

// ReferenceCapture independently interprets the bounded signed test box using exact int64 data.
func ReferenceCapture(q, c, d, n int64) (int64, int64, int64, bool) {
	steps, events := int64(0), int64(0)
	for n%c != 0 {
		if steps >= 56 {
			return n, steps, events, false
		}
		if n%d == 0 {
			n /= d
		} else {
			n = q*n + c
			events++
		}
		steps++
	}
	return n, steps, events, true
}

// ReferenceAdmissible independently checks the small box using bounded integer arithmetic.
func ReferenceAdmissible(q, c, d, k int64) bool {
	if c == 0 || k < 0 || (d > -2 && d < 2) {
		return false
	}
	a, b := c, d
	if a < 0 {
		a = -a
	}
	if b < 0 {
		b = -b
	}
	for b != 0 {
		a, b = b, a%b
	}
	power := int64(1)
	for i := int64(0); i < k; i++ {
		power *= q
	}
	return a == 1 && power%c == 0
}

// TestSignedBox checks a proved finite box: at most 3 affine events and |state| <= 5620.
func TestSignedBox(t *testing.T) {
	var w Workspace
	var seed big.Int
	var certificate Certificate
	count := 0
	for q := int64(-5); q <= 5; q++ {
		for c := int64(-20); c <= 20; c++ {
			if c == 0 {
				continue
			}
			for d := int64(-6); d <= 6; d++ {
				if d > -2 && d < 2 {
					continue
				}
				for k := int64(0); k <= 3; k++ {
					p, err := ParseParameters(strconv.FormatInt(q, 10),
						strconv.FormatInt(c, 10), strconv.FormatInt(d, 10),
						strconv.FormatInt(k, 10))
					admissible := ReferenceAdmissible(q, c, d, k)
					if (err == nil) != admissible {
						t.Fatalf("parameter mismatch: (%d,%d,%d), k=%d", q, c, d, k)
					}
					if !admissible {
						continue
					}
					for n := int64(-40); n <= 40; n++ {
						seed.SetInt64(n)
						entry, steps, events, terminated := ReferenceCapture(q, c, d, n)
						if !terminated {
							t.Fatal("reference exceeded its proved raw-time bound")
						}
						if err := Capture(&p, &seed, &certificate, &w); err != nil {
							t.Fatal(err)
						}
						if !certificate.Entry.IsInt64() || certificate.Entry.Int64() != entry ||
							!certificate.Steps.IsInt64() || certificate.Steps.Int64() != steps ||
							!certificate.AffineEvents.IsInt64() ||
							certificate.AffineEvents.Int64() != events || events > k {
							t.Fatalf("entry mismatch: (%d,%d,%d), k=%d, n=%d", q, c, d, k, n)
						}
						if !certificate.Normalized.IsInt64() ||
							certificate.Normalized.Int64() != entry/c {
							t.Fatal("normalization changed the signed exact quotient")
						}
						if err := CheckTail(&p, &certificate, 8); err != nil {
							t.Fatal(err)
						}
						count++
					}
				}
			}
		}
	}
	if count != 160056 {
		t.Fatalf("finite parameter box changed: got %d certificates, want 160056", count)
	}
	t.Logf("checked %d signed first-entry certificates and eight-step tails", count)
}

// TestRejectedParameters separates missing hypotheses from admissible boundary cases.
func TestRejectedParameters(t *testing.T) {
	invalid := [][4]string{
		{"3", "9", "0", "2"}, {"3", "9", "1", "2"},
		{"3", "9", "-1", "2"}, {"3", "0", "2", "2"},
		{"2", "2", "-2", "1"}, {"3", "5", "2", "2"},
		{"3", "9", "2", "-1"}, {"", "1", "2", "0"},
		{"3", "1.0", "2", "0"}, {"3", "1", "2", "1.5"},
	}
	for _, values := range invalid {
		if _, err := ParseParameters(values[0], values[1], values[2], values[3]); err == nil {
			t.Fatalf("accepted invalid arithmetic witness: %v", values)
		}
	}
	for _, values := range [][4]string{
		{"0", "10", "-3", "1"}, {"-1", "-1", "-2", "0"},
		{"0", "1", "2", "0"}, {"3", "-9", "-2", "2"},
	} {
		if _, err := ParseParameters(values[0], values[1], values[2], values[3]); err != nil {
			t.Fatal(err)
		}
	}
}

// TestLargeEntry checks a two-event certificate with signed 70-bit division and 260-bit offset.
func TestLargeEntry(t *testing.T) {
	var q, c, d, seed, expectedUnit, expectedEntry big.Int
	q.Lsh(big.NewInt(1), 130)
	q.Add(&q, big.NewInt(3))
	c.Mul(&q, &q)
	d.Lsh(big.NewInt(1), 70)
	d.Neg(&d)
	seed.Lsh(big.NewInt(1), 100)
	seed.Add(&seed, big.NewInt(1))
	expectedUnit.Add(&seed, &q)
	expectedUnit.Add(&expectedUnit, big.NewInt(1))
	expectedEntry.Mul(&c, &expectedUnit)
	p, err := ParseParameters(q.String(), c.String(), d.String(), "2")
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	var certificate Certificate
	if err := Capture(&p, &seed, &certificate, &w); err != nil {
		t.Fatal(err)
	}
	if certificate.Entry.Cmp(&expectedEntry) != 0 ||
		certificate.Normalized.Cmp(&expectedUnit) != 0 ||
		certificate.Steps.Cmp(big.NewInt(2)) != 0 ||
		certificate.AffineEvents.Cmp(big.NewInt(2)) != 0 {
		t.Fatal("large certificate disagrees with c*(seed+q+1)")
	}
	if err := CheckTail(&p, &certificate, 16); err != nil {
		t.Fatal(err)
	}
}

// TestTailBoundaries checks the time-zero equation and rejects invalid finite-tail requests.
func TestTailBoundaries(t *testing.T) {
	p, err := ParseParameters("3", "9", "2", "2")
	if err != nil {
		t.Fatal(err)
	}
	var certificate Certificate
	certificate.Entry.SetInt64(18)
	certificate.Normalized.SetInt64(2)
	if err := CheckTail(&p, &certificate, 0); err != nil {
		t.Fatal(err)
	}
	if err := CheckTail(&p, &certificate, -1); err == nil {
		t.Fatal("negative tail length was accepted")
	}
	certificate.Normalized.SetInt64(3)
	if err := CheckTail(&p, &certificate, 0); err == nil {
		t.Fatal("time-zero scaling mismatch was accepted")
	}
	var invalid Parameters
	if err := CheckTail(&invalid, &certificate, 0); err == nil {
		t.Fatal("unvalidated parameters were accepted")
	}
}

// TestFirstEntryAliasing permits the input seed to occupy either caller-owned state field.
func TestFirstEntryAliasing(t *testing.T) {
	p, err := ParseParameters("3", "9", "2", "2")
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	var certificate Certificate
	for _, seed := range []*big.Int{&certificate.Entry, &certificate.Normalized} {
		seed.SetInt64(1)
		if err := Capture(&p, seed, &certificate, &w); err != nil {
			t.Fatal(err)
		}
		if certificate.Entry.Cmp(big.NewInt(18)) != 0 ||
			certificate.Normalized.Cmp(big.NewInt(2)) != 0 ||
			certificate.Steps.Cmp(big.NewInt(4)) != 0 ||
			certificate.AffineEvents.Cmp(big.NewInt(2)) != 0 {
			t.Fatal("aliased seed changed the first-entry certificate")
		}
	}
}

// TestControls independently runs the four exact certificate and tail controls.
func TestControls(t *testing.T) {
	if err := RunChecks(); err != nil {
		t.Fatal(err)
	}
}
