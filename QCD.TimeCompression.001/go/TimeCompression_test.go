// SPDX-License-Identifier: CC-BY-4.0

package main

import (
	"math"
	"math/big"
	"strconv"
	"testing"
)

// ReferenceStep applies the bounded signed raw map without using production code.
func ReferenceStep(n, q, c, d int64) (int64, bool) {
	if n%d == 0 {
		return n / d, false
	}
	return q*n + c, true
}

// ReferencePower computes a small nonnegative signed power.
func ReferencePower(d int64, a uint64) int64 {
	factor := int64(1)
	for i := uint64(0); i < a; i++ {
		factor *= d
	}
	return factor
}

// ReferenceTrajectory expands each bounded compressed step directly.
func ReferenceTrajectory(
	n, q, c, d int64,
	a, compressedSteps uint64,
) (int64, uint64, uint64) {
	factor := ReferencePower(d, a)
	originalQ := factor * q
	originalC := factor * c
	state := n
	rawSteps := uint64(0)
	affineEvents := uint64(0)
	for i := uint64(0); i < compressedSteps; i++ {
		boundary := state
		var affine bool
		state, affine = ReferenceStep(state, q, c, d)
		if !affine {
			raw, _ := ReferenceStep(boundary, originalQ, originalC, d)
			if raw != state {
				panic("reference division block mismatch")
			}
			rawSteps++
			continue
		}

		raw, rawAffine := ReferenceStep(boundary, originalQ, originalC, d)
		if !rawAffine {
			panic("reference affine guard mismatch")
		}
		for j := uint64(0); j < a; j++ {
			var divided bool
			raw, divided = ReferenceStep(raw, originalQ, originalC, d)
			if divided {
				panic("reference forced division was not taken")
			}
		}
		if raw != state {
			panic("reference affine block mismatch")
		}
		affineEvents++
		rawSteps += a + 1
	}
	return state, rawSteps, affineEvents
}

// TestExhaustiveBoundedBlocks compares every bounded certificate with an independent model.
func TestExhaustiveBoundedBlocks(t *testing.T) {
	divisors := []int64{-4, -3, -2, 2, 3, 4}
	certificateCount := 0
	for q := int64(-2); q <= 2; q++ {
		for c := int64(-2); c <= 2; c++ {
			for _, d := range divisors {
				for a := uint64(0); a <= 2; a++ {
					factor := ReferencePower(d, a)
					p, err := ParseParameters(
						strconv.FormatInt(factor*q, 10),
						strconv.FormatInt(factor*c, 10),
						strconv.FormatInt(d, 10),
						strconv.FormatInt(q, 10),
						strconv.FormatInt(c, 10),
						a,
					)
					if err != nil {
						t.Fatalf("valid parameters rejected: %v", err)
					}
					for n := int64(-15); n <= 15; n++ {
						for k := uint64(0); k <= 6; k++ {
							wantState, wantRaw, wantAffine :=
								ReferenceTrajectory(n, q, c, d, a, k)
							seed := big.NewInt(n)
							var certificate Certificate
							var w Workspace
							if err := CheckTrajectory(&p, seed, k, &certificate, &w); err != nil {
								t.Fatalf("certificate failed: %v", err)
							}
							if !certificate.Endpoint.IsInt64() ||
								certificate.Endpoint.Int64() != wantState {
								t.Fatalf(
									"q=%d c=%d d=%d a=%d n=%d k=%d endpoint=%s, want %d",
									q, c, d, a, n, k, &certificate.Endpoint, wantState,
								)
							}
							if !certificate.RawSteps.IsUint64() ||
								certificate.RawSteps.Uint64() != wantRaw {
								t.Fatalf("raw steps=%s, want %d", &certificate.RawSteps, wantRaw)
							}
							if certificate.AffineEvents != wantAffine {
								t.Fatalf("affine events=%d, want %d", certificate.AffineEvents, wantAffine)
							}
							if wantRaw != k+a*wantAffine {
								t.Fatalf("clock identity failed: %d != %d+%d*%d", wantRaw, k, a, wantAffine)
							}
							certificateCount++
						}
					}
				}
			}
		}
	}
	if certificateCount != 97650 {
		t.Fatalf("checked %d certificates, want 97650", certificateCount)
	}
}

// TestLargeSignedArithmetic checks exact block expansion beyond fixed-width integers.
func TestLargeSignedArithmetic(t *testing.T) {
	d := new(big.Int).Lsh(big.NewInt(1), 70)
	d.Neg(d)
	q := new(big.Int).Lsh(big.NewInt(1), 130)
	q.Add(q, big.NewInt(3))
	c := new(big.Int).Lsh(big.NewInt(1), 100)
	c.Neg(c)
	c.Add(c, big.NewInt(5))
	factor := new(big.Int).Exp(d, big.NewInt(3), nil)
	originalQ := new(big.Int).Mul(factor, q)
	originalC := new(big.Int).Mul(factor, c)
	p, err := ParseParameters(
		originalQ.String(),
		originalC.String(),
		d.String(),
		q.String(),
		c.String(),
		3,
	)
	if err != nil {
		t.Fatal(err)
	}
	seed := new(big.Int).Lsh(big.NewInt(1), 90)
	seed.Add(seed, big.NewInt(1))
	want := new(big.Int).Mul(q, seed)
	want.Add(want, c)
	want.Mul(q, want)
	want.Add(want, c)
	var certificate Certificate
	var w Workspace
	if err := CheckTrajectory(&p, seed, 2, &certificate, &w); err != nil {
		t.Fatal(err)
	}
	if certificate.Endpoint.Cmp(want) != 0 {
		t.Fatalf("large endpoint=%s, want %s", &certificate.Endpoint, want)
	}
	if certificate.RawSteps.Cmp(big.NewInt(8)) != 0 || certificate.AffineEvents != 2 {
		t.Fatalf("large clock=(%s,%d), want (8,2)", &certificate.RawSteps, certificate.AffineEvents)
	}
}

// TestAliasingAndOwnedCertificate checks supported in-place output and result ownership.
func TestAliasingAndOwnedCertificate(t *testing.T) {
	p, err := ParseParameters("4", "4", "2", "1", "1", 2)
	if err != nil {
		t.Fatal(err)
	}
	state := big.NewInt(1)
	var w Workspace
	steps, affine, err := AdvanceBlock(&p, state, state, &w)
	if err != nil {
		t.Fatal(err)
	}
	if state.Cmp(big.NewInt(2)) != 0 || steps != 3 || !affine {
		t.Fatalf("in-place block=(%s,%d,%t), want (2,3,true)", state, steps, affine)
	}

	var certificate Certificate
	certificate.Endpoint.SetInt64(1)
	if err := CheckTrajectory(&p, &certificate.Endpoint, 3, &certificate, &w); err != nil {
		t.Fatal(err)
	}
	endpoint := new(big.Int).Set(&certificate.Endpoint)
	rawSteps := new(big.Int).Set(&certificate.RawSteps)
	p.Q.SetInt64(999)
	if certificate.Endpoint.Cmp(endpoint) != 0 || certificate.RawSteps.Cmp(rawSteps) != 0 {
		t.Fatal("certificate aliases parameters or transient workspace state")
	}
}

// TestRejectedParameters checks every declared validation boundary.
func TestRejectedParameters(t *testing.T) {
	cases := []struct {
		q           string
		c           string
		d           string
		compressedQ string
		compressedC string
		a           uint64
	}{
		{"2", "2", "1", "1", "1", 1},
		{"3", "2", "2", "1", "1", 1},
		{"2", "3", "2", "1", "1", 1},
		{"0", "0", "2", "0", "0", math.MaxUint64},
	}
	for _, test := range cases {
		if _, err := ParseParameters(
			test.q,
			test.c,
			test.d,
			test.compressedQ,
			test.compressedC,
			test.a,
		); err == nil {
			t.Fatalf("accepted invalid parameters %+v", test)
		}
	}
	if _, err := ParseParameters("x", "0", "2", "0", "0", 0); err == nil {
		t.Fatal("accepted a malformed integer")
	}
	var w Workspace
	if err := ValidateParameters(nil, &w); err == nil {
		t.Fatal("accepted nil parameters")
	}
	p, err := ParseParameters("1", "1", "2", "1", "1", 0)
	if err != nil {
		t.Fatal(err)
	}
	if _, _, err := AdvanceBlock(&p, nil, big.NewInt(0), &w); err == nil {
		t.Fatal("accepted a nil input state")
	}
	if err := CheckTrajectory(&p, big.NewInt(0), 0, nil, &w); err == nil {
		t.Fatal("accepted a nil certificate")
	}
}

// TestRunChecks executes the documented exact controls.
func TestRunChecks(t *testing.T) {
	if err := RunChecks(); err != nil {
		t.Fatal(err)
	}
}
