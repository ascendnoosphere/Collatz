// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// ReferenceCertificate uses machine-word arithmetic and scans every access residue.
func ReferenceCertificate(c, d, n int64) (int64, int64, uint64, uint64, Outcome) {
	a, g := c, d
	for a != 0 {
		a, g = g%a, a
	}
	l := d / g
	b := c * (l - 1)
	core := b / (d - 1)
	epsilon := (d-1)*(core+1) - b
	defect := (d-1)*n - b
	power := epsilon
	var budget uint64
	for power <= defect {
		power *= d
		budget++
	}
	current, rawTime := n, int64(0)
	var blocks uint64
	// This oracle does not use the modular inverse or the arbitrary-precision builder.
	for current%g == 0 && current > core {
		var ell int64
		for (current+ell*c)%d != 0 {
			ell++
			if ell >= l {
				panic("reference access window exhausted")
			}
		}
		current = (current + ell*c) / d
		rawTime += ell + 1
		blocks++
	}
	outcome := CoreOutcome
	if current%g != 0 {
		outcome = TrapOutcome
	}
	return current, rawTime, blocks, budget, outcome
}

// TestReferenceCertificates compares every field with an independent bounded oracle.
func TestReferenceCertificates(t *testing.T) {
	var w Workspace
	var certificate Certificate
	var c, d, seed, expected big.Int
	for divisor := int64(2); divisor <= 24; divisor++ {
		d.SetInt64(divisor)
		for offset := int64(1); offset <= 16; offset++ {
			c.SetInt64(offset)
			m, err := NewMap(&c, &d)
			if err != nil {
				t.Fatal(err)
			}
			for n := int64(1); n <= 128; n++ {
				seed.SetInt64(n)
				if err := m.BuildCertificateInto(&certificate, &seed, &w); err != nil {
					t.Fatalf("c=%d D=%d n=%d: %v", offset, divisor, n, err)
				}
				reached, clock, blocks, budget, outcome :=
					ReferenceCertificate(offset, divisor, n)
				expected.SetInt64(reached)
				if certificate.Reached.Cmp(&expected) != 0 {
					t.Fatalf("c=%d D=%d n=%d: wrong endpoint", offset, divisor, n)
				}
				expected.SetInt64(clock)
				if certificate.RawTime.Cmp(&expected) != 0 || certificate.Blocks != blocks ||
					certificate.Budget != budget || certificate.Outcome != outcome {
					t.Fatalf("c=%d D=%d n=%d: wrong metadata", offset, divisor, n)
				}
				if err := m.VerifyCertificate(&certificate, &w); err != nil {
					t.Fatal(err)
				}
				if blocks > budget || clock > int64(blocks)*(divisor/Gcd(offset, divisor)) {
					t.Fatal("geometric or raw-clock bound violated")
				}
			}
		}
	}
}

// Gcd computes the independent oracle's positive Euclidean gcd.
func Gcd(a, b int64) int64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// TestRawReplay checks exact raw endpoints and continued affine-only trap tails.
func TestRawReplay(t *testing.T) {
	cases := [][3]int64{{3, 2, 80}, {6, 4, 4}, {2, 4, 2}, {10, 6, 100}, {8, 8, 512}}
	for _, parameters := range cases {
		m, err := NewMap(big.NewInt(parameters[0]), big.NewInt(parameters[1]))
		if err != nil {
			t.Fatal(err)
		}
		var w Workspace
		seed := big.NewInt(parameters[2])
		certificate, err := m.BuildCertificate(seed, &w)
		if err != nil {
			t.Fatal(err)
		}
		var state, expected big.Int
		state.Set(seed)
		for time := int64(0); time < certificate.RawTime.Int64(); time++ {
			if err := m.Step(&state, &state, &w); err != nil {
				t.Fatal(err)
			}
		}
		if state.Cmp(&certificate.Reached) != 0 {
			t.Fatal("raw replay endpoint differs")
		}
		if certificate.Outcome == TrapOutcome {
			expected.Set(&state)
			for j := 0; j < 32; j++ {
				expected.Add(&expected, &m.c)
				if err := m.Step(&state, &state, &w); err != nil {
					t.Fatal(err)
				}
				if state.Cmp(&expected) != 0 {
					t.Fatal("inaccessible tail was not affine-only")
				}
			}
		}
	}
}

// TestCertificateTampering checks every field and snapshots all rejected inputs.
func TestCertificateTampering(t *testing.T) {
	m, err := NewMap(big.NewInt(3), big.NewInt(2))
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	var certificate, before Certificate
	var seed big.Int
	seed.SetInt64(200)
	for field := 0; field < 6; field++ {
		if err := m.BuildCertificateInto(&certificate, &seed, &w); err != nil {
			t.Fatal(err)
		}
		// Tampering is isolated per field and never uses a shallow big.Int copy.
		switch field {
		case 0:
			certificate.Seed.SetInt64(0)
		case 1:
			certificate.Reached.Add(&certificate.Reached, big.NewInt(1))
		case 2:
			certificate.RawTime.Add(&certificate.RawTime, big.NewInt(1))
		case 3:
			certificate.Blocks++
		case 4:
			certificate.Budget++
		case 5:
			certificate.Outcome = TrapOutcome
		}
		before.Seed.Set(&certificate.Seed)
		before.Reached.Set(&certificate.Reached)
		before.RawTime.Set(&certificate.RawTime)
		before.Blocks, before.Budget, before.Outcome =
			certificate.Blocks, certificate.Budget, certificate.Outcome
		if err := m.VerifyCertificate(&certificate, &w); err == nil {
			t.Fatalf("accepted tampered field %d", field)
		}
		if certificate.Seed.Cmp(&before.Seed) != 0 ||
			certificate.Reached.Cmp(&before.Reached) != 0 ||
			certificate.RawTime.Cmp(&before.RawTime) != 0 ||
			certificate.Blocks != before.Blocks || certificate.Budget != before.Budget ||
			certificate.Outcome != before.Outcome {
			t.Fatal("verification mutated its rejected input")
		}
	}
}

// TestInputOwnershipAndAliases checks independent constants and caller-visible field aliases.
func TestInputOwnershipAndAliases(t *testing.T) {
	c, d := big.NewInt(3), big.NewInt(2)
	m, err := NewMap(c, d)
	if err != nil {
		t.Fatal(err)
	}
	c.SetInt64(100)
	d.SetInt64(100)
	var w Workspace
	var certificate Certificate
	for field := 0; field < 3; field++ {
		var seed *big.Int
		switch field {
		case 0:
			seed = &certificate.Seed
		case 1:
			seed = &certificate.Reached
		case 2:
			seed = &certificate.RawTime
		}
		seed.SetInt64(80)
		if err := m.BuildCertificateInto(&certificate, seed, &w); err != nil {
			t.Fatal(err)
		}
		if certificate.Seed.Cmp(big.NewInt(80)) != 0 {
			t.Fatal("builder lost its aliased input")
		}
		if err := m.VerifyCertificate(&certificate, &w); err != nil {
			t.Fatal(err)
		}
	}
	seed := big.NewInt(80)
	if err := m.BuildCertificateInto(&certificate, seed, &w); err != nil {
		t.Fatal(err)
	}
	seed.SetInt64(1)
	if certificate.Seed.Cmp(big.NewInt(80)) != 0 {
		t.Fatal("certificate retained source seed storage")
	}
	if err := m.Divisor(d); err != nil {
		t.Fatal(err)
	}
	d.SetInt64(100)
	if err := m.VerifyCertificate(&certificate, &w); err != nil {
		t.Fatal("divisor output exposed map storage")
	}
}

// TestLargeClock verifies raw times exceeding machine words and success nonmutation.
func TestLargeClock(t *testing.T) {
	var d, expectedTime big.Int
	d.Lsh(big.NewInt(1), 100)
	m, err := NewMap(big.NewInt(1), &d)
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	certificate, err := m.BuildCertificate(big.NewInt(2), &w)
	if err != nil {
		t.Fatal(err)
	}
	expectedTime.Sub(&d, big.NewInt(1))
	if certificate.RawTime.Cmp(&expectedTime) != 0 || certificate.Reached.Int64() != 1 ||
		certificate.Blocks != 1 || certificate.Budget != 1 || certificate.Outcome != CoreOutcome {
		t.Fatal("large-clock certificate differs from its exact one-block formula")
	}
	var before Certificate
	before.Seed.Set(&certificate.Seed)
	before.Reached.Set(&certificate.Reached)
	before.RawTime.Set(&certificate.RawTime)
	before.Blocks, before.Budget, before.Outcome =
		certificate.Blocks, certificate.Budget, certificate.Outcome
	if err := m.VerifyCertificate(&certificate, &w); err != nil {
		t.Fatal(err)
	}
	if certificate.Seed.Cmp(&before.Seed) != 0 ||
		certificate.Reached.Cmp(&before.Reached) != 0 ||
		certificate.RawTime.Cmp(&before.RawTime) != 0 ||
		certificate.Blocks != before.Blocks || certificate.Budget != before.Budget ||
		certificate.Outcome != before.Outcome {
		t.Fatal("verification mutated its successful input")
	}
}

// TestLargeZeroCore checks trapping with a multiword gcd and an exact strict threshold.
func TestLargeZeroCore(t *testing.T) {
	var c, d big.Int
	c.Lsh(big.NewInt(1), 80)
	d.Lsh(big.NewInt(1), 82)
	m, err := NewMap(&c, &d)
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	certificate, err := m.BuildCertificate(&c, &w)
	if err != nil {
		t.Fatal(err)
	}
	if certificate.Reached.Int64() != 1 || certificate.RawTime.Int64() != 4 ||
		certificate.Blocks != 1 || certificate.Budget != 2 || certificate.Outcome != TrapOutcome {
		t.Fatal("multiword zero-core certificate differs from the exact formula")
	}
	if err := m.VerifyCertificate(&certificate, &w); err != nil {
		t.Fatal(err)
	}
}

// TestWarmedAllocations requires buffer reuse throughout the successful hot path.
func TestWarmedAllocations(t *testing.T) {
	m, err := NewMap(big.NewInt(7), big.NewInt(12))
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	var certificate Certificate
	seed := big.NewInt(4000)
	if err := m.BuildCertificateInto(&certificate, seed, &w); err != nil {
		t.Fatal(err)
	}
	if err := m.VerifyCertificate(&certificate, &w); err != nil {
		t.Fatal(err)
	}
	allocations := testing.AllocsPerRun(1000, func() {
		if err := m.BuildCertificateInto(&certificate, seed, &w); err != nil {
			panic(err)
		}
		if err := m.VerifyCertificate(&certificate, &w); err != nil {
			panic(err)
		}
	})
	if allocations != 0 {
		t.Fatalf("warmed path allocated %.2f objects per run", allocations)
	}
}

// TestValidationBoundaries checks map/certificate pointer inputs and invalid receivers.
func TestValidationBoundaries(t *testing.T) {
	if _, err := NewMap(nil, big.NewInt(2)); err == nil {
		t.Fatal("accepted nil offset")
	}
	if _, err := NewMap(big.NewInt(1), big.NewInt(1)); err == nil {
		t.Fatal("accepted divisor one")
	}
	m, err := NewMap(big.NewInt(1), big.NewInt(2))
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	var state big.Int
	var certificate Certificate
	state.SetInt64(1)
	maps := []*Map{nil, new(Map)}
	for _, invalid := range maps {
		if invalid.Step(&state, &state, &w) == nil ||
			invalid.BuildCertificateInto(&certificate, &state, &w) == nil ||
			invalid.VerifyCertificate(&certificate, &w) == nil {
			t.Fatal("accepted invalid receiver")
		}
	}
	if m.Step(nil, &state, &w) == nil || m.Step(&state, nil, &w) == nil ||
		m.Step(&state, &state, nil) == nil || m.Divisor(nil) == nil || m.CoreRadius(nil) == nil {
		t.Fatal("accepted nil step or copy argument")
	}
	if m.BuildCertificateInto(nil, &state, &w) == nil ||
		m.BuildCertificateInto(&certificate, nil, &w) == nil ||
		m.BuildCertificateInto(&certificate, &state, nil) == nil ||
		m.VerifyCertificate(nil, &w) == nil || m.VerifyCertificate(&certificate, nil) == nil {
		t.Fatal("accepted nil certificate argument")
	}
	if _, err := m.GeometricBudget(nil, &w); err == nil {
		t.Fatal("accepted nil budget seed")
	}
	if _, err := m.GeometricBudget(&state, nil); err == nil {
		t.Fatal("accepted nil budget workspace")
	}
	state.SetInt64(0)
	if m.Capture(&state, &w) == nil {
		t.Fatal("accepted zero seed")
	}
}
