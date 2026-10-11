// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// TestExhaustiveUnitCertificates checks exact decomposition on a bounded family.
func TestExhaustiveUnitCertificates(t *testing.T) {
	var workspace Workspace
	var seed big.Int
	var divisorInt big.Int
	var expectedInt big.Int
	var certificate Certificate
	for divisor := uint64(2); divisor <= 64; divisor++ {
		divisorInt.SetUint64(divisor)
		m, err := NewMap(&divisorInt)
		if err != nil {
			t.Fatal(err)
		}
		for n := uint64(1); n <= 2048; n++ {
			seed.SetUint64(n)
			if err := m.BuildCertificateInto(&certificate, &seed, &workspace); err != nil {
				t.Fatalf("D=%d n=%d: %v", divisor, n, err)
			}
			if err := m.VerifyCertificate(&certificate, &workspace); err != nil {
				t.Fatalf("D=%d n=%d: %v", divisor, n, err)
			}

			// Compare with an independent machine-word decomposition.
			expected := n
			var exponent uint64
			for expected%divisor == 0 {
				expected /= divisor
				exponent++
			}
			expectedInt.SetUint64(expected)
			if certificate.Fixed.Cmp(&expectedInt) != 0 {
				t.Fatalf("D=%d n=%d: fixed=%s", divisor, n, certificate.Fixed.String())
			}
			if certificate.EntryTime != exponent {
				t.Fatalf("D=%d n=%d: entry=%d", divisor, n, certificate.EntryTime)
			}
		}
	}
}

// TestLargeEntry checks a 300-division arbitrary-precision orbit.
func TestLargeEntry(t *testing.T) {
	m, err := NewMap(big.NewInt(37))
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	seed := new(big.Int).Exp(big.NewInt(37), big.NewInt(300), nil)
	seed.Mul(seed, big.NewInt(53))
	certificate, err := m.BuildCertificate(seed, &workspace)
	if err != nil {
		t.Fatal(err)
	}
	if certificate.EntryTime != 300 || certificate.Fixed.Cmp(big.NewInt(53)) != 0 {
		t.Fatalf("entry=%d fixed=%s", certificate.EntryTime, certificate.Fixed.String())
	}
	if err := m.VerifyCertificate(&certificate, &workspace); err != nil {
		t.Fatal(err)
	}
}

// TestFixedClassification checks fixed and strict-division branches for a composite divisor.
func TestFixedClassification(t *testing.T) {
	m, err := NewMap(big.NewInt(6))
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	var next big.Int
	for n := int64(1); n <= 120; n++ {
		state := big.NewInt(n)
		if err := m.Step(&next, state, &workspace); err != nil {
			t.Fatal(err)
		}
		if n%6 == 0 && next.Cmp(state) >= 0 {
			t.Fatalf("divisible state %d did not decrease", n)
		}
		if n%6 != 0 && next.Cmp(state) != 0 {
			t.Fatalf("base-free state %d was not fixed", n)
		}
	}
}

// TestInPlaceStep checks that the step operation permits destination-source aliasing.
func TestInPlaceStep(t *testing.T) {
	m, err := NewMap(big.NewInt(10))
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	state := big.NewInt(700)
	if err := m.Step(state, state, &workspace); err != nil {
		t.Fatal(err)
	}
	if state.Cmp(big.NewInt(70)) != 0 {
		t.Fatalf("in-place division produced %s", state.String())
	}
	state.SetInt64(71)
	if err := m.Step(state, state, &workspace); err != nil {
		t.Fatal(err)
	}
	if state.Cmp(big.NewInt(71)) != 0 {
		t.Fatalf("in-place fixed branch produced %s", state.String())
	}
}

// TestTamperedCertificate checks rejection without repairing the supplied certificate.
func TestTamperedCertificate(t *testing.T) {
	m, err := NewMap(big.NewInt(5))
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	certificate, err := m.BuildCertificate(big.NewInt(1250), &workspace)
	if err != nil {
		t.Fatal(err)
	}
	certificate.EntryTime++
	if err := m.VerifyCertificate(&certificate, &workspace); err == nil {
		t.Fatal("accepted altered entry time")
	}
	certificate.EntryTime--
	certificate.Fixed.Add(&certificate.Fixed, big.NewInt(1))
	var altered big.Int
	altered.Set(&certificate.Fixed)
	if err := m.VerifyCertificate(&certificate, &workspace); err == nil {
		t.Fatal("accepted altered fixed point")
	}
	if certificate.Fixed.Cmp(&altered) != 0 {
		t.Fatal("verification mutated the rejected certificate")
	}
}

// TestReusableAllocations checks that the warmed build-and-verify path allocates nothing.
func TestReusableAllocations(t *testing.T) {
	m, err := NewMap(big.NewInt(8))
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	var certificate Certificate
	seed := big.NewInt(4096)
	if err := m.BuildCertificateInto(&certificate, seed, &workspace); err != nil {
		t.Fatal(err)
	}
	if err := m.VerifyCertificate(&certificate, &workspace); err != nil {
		t.Fatal(err)
	}
	allocations := testing.AllocsPerRun(1000, func() {
		if err := m.BuildCertificateInto(&certificate, seed, &workspace); err != nil {
			panic(err)
		}
		if err := m.VerifyCertificate(&certificate, &workspace); err != nil {
			panic(err)
		}
	})
	if allocations != 0 {
		t.Fatalf("warmed path allocated %.2f objects per run", allocations)
	}
}

// TestInvalidInputs checks public validation boundaries.
func TestInvalidInputs(t *testing.T) {
	if _, err := NewMap(nil); err == nil {
		t.Fatal("accepted nil divisor")
	}
	if _, err := NewMap(big.NewInt(1)); err == nil {
		t.Fatal("accepted divisor one")
	}
	m, err := NewMap(big.NewInt(2))
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	var state big.Int
	if err := m.Step(&state, &state, &workspace); err == nil {
		t.Fatal("accepted zero state")
	}
	if err := m.BuildCertificateInto(nil, big.NewInt(1), &workspace); err == nil {
		t.Fatal("accepted nil certificate")
	}
	if _, err := m.BuildCertificate(big.NewInt(-1), &workspace); err == nil {
		t.Fatal("accepted negative seed")
	}
	if err := m.VerifyCertificate(nil, &workspace); err == nil {
		t.Fatal("accepted nil certificate verification")
	}
}

// TestInvalidMaps checks every public method on nil and uninitialized receivers.
func TestInvalidMaps(t *testing.T) {
	one := &Map{}
	one.d.SetInt64(1)
	negative := &Map{}
	negative.d.SetInt64(-2)
	maps := []*Map{nil, {}, one, negative}
	for i, m := range maps {
		var workspace Workspace
		var dst big.Int
		state := big.NewInt(1)
		certificate := Certificate{}
		certificate.Seed.SetInt64(1)
		certificate.Fixed.SetInt64(1)
		if err := m.Validate(); err == nil {
			t.Fatalf("receiver %d passed validation", i)
		}
		if err := m.Divisor(&dst); err == nil {
			t.Fatalf("receiver %d exposed an invalid divisor", i)
		}
		if err := m.Step(&dst, state, &workspace); err == nil {
			t.Fatalf("receiver %d stepped", i)
		}
		if _, err := m.Decompose(&dst, state, &workspace); err == nil {
			t.Fatalf("receiver %d decomposed", i)
		}
		if err := m.BuildCertificateInto(&certificate, state, &workspace); err == nil {
			t.Fatalf("receiver %d built into storage", i)
		}
		if _, err := m.BuildCertificate(state, &workspace); err == nil {
			t.Fatalf("receiver %d built a certificate", i)
		}
		if err := m.VerifyCertificate(&certificate, &workspace); err == nil {
			t.Fatalf("receiver %d verified a certificate", i)
		}
	}
}

// TestNilArguments locks down the error contract for pointer-valued arguments.
func TestNilArguments(t *testing.T) {
	m, err := NewMap(big.NewInt(5))
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	var dst big.Int
	seed := big.NewInt(1250)
	certificate, err := m.BuildCertificate(seed, &workspace)
	if err != nil {
		t.Fatal(err)
	}

	// These calls must return errors before dereferencing the invalid argument.
	cases := []struct {
		name  string
		check func() error
	}{
		{"divisor destination", func() error { return m.Divisor(nil) }},
		{"step destination", func() error { return m.Step(nil, seed, &workspace) }},
		{"step state", func() error { return m.Step(&dst, nil, &workspace) }},
		{"step workspace", func() error { return m.Step(&dst, seed, nil) }},
		{"decompose factor", func() error {
			_, err := m.Decompose(nil, seed, &workspace)
			return err
		}},
		{"decompose state", func() error {
			_, err := m.Decompose(&dst, nil, &workspace)
			return err
		}},
		{"decompose workspace", func() error {
			_, err := m.Decompose(&dst, seed, nil)
			return err
		}},
		{"build destination", func() error {
			return m.BuildCertificateInto(nil, seed, &workspace)
		}},
		{"build seed", func() error {
			return m.BuildCertificateInto(&certificate, nil, &workspace)
		}},
		{"build workspace", func() error {
			return m.BuildCertificateInto(&certificate, seed, nil)
		}},
		{"owned build seed", func() error {
			_, err := m.BuildCertificate(nil, &workspace)
			return err
		}},
		{"owned build workspace", func() error {
			_, err := m.BuildCertificate(seed, nil)
			return err
		}},
		{"verify certificate", func() error { return m.VerifyCertificate(nil, &workspace) }},
		{"verify workspace", func() error { return m.VerifyCertificate(&certificate, nil) }},
	}
	for _, item := range cases {
		if err := item.check(); err == nil {
			t.Fatalf("accepted nil %s", item.name)
		}
	}
}

// TestIndependentOwnership checks that caller mutations do not alter maps or certificates.
func TestIndependentOwnership(t *testing.T) {
	divisor := big.NewInt(5)
	m, err := NewMap(divisor)
	if err != nil {
		t.Fatal(err)
	}
	divisor.SetInt64(7)
	var copied big.Int
	if err := m.Divisor(&copied); err != nil {
		t.Fatal(err)
	}
	if copied.Cmp(big.NewInt(5)) != 0 {
		t.Fatal("map aliases its constructor input")
	}
	copied.SetInt64(1)
	if err := m.Divisor(&copied); err != nil {
		t.Fatal(err)
	}
	if copied.Cmp(big.NewInt(5)) != 0 {
		t.Fatal("divisor output aliases the map")
	}

	var workspace Workspace
	seed := big.NewInt(1250)
	certificate, err := m.BuildCertificate(seed, &workspace)
	if err != nil {
		t.Fatal(err)
	}
	seed.SetInt64(1)
	if certificate.Seed.Cmp(big.NewInt(1250)) != 0 {
		t.Fatal("certificate aliases its seed input")
	}
	if certificate.Fixed.Cmp(big.NewInt(2)) != 0 || certificate.EntryTime != 4 {
		t.Fatal("certificate has the wrong independent normal form")
	}
	if err := m.VerifyCertificate(&certificate, &workspace); err != nil {
		t.Fatal(err)
	}
}

// TestCallerAliases covers supported in-place decomposition and certificate-field seeds.
func TestCallerAliases(t *testing.T) {
	m, err := NewMap(big.NewInt(5))
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	factor := big.NewInt(1250)
	entry, err := m.Decompose(factor, factor, &workspace)
	if err != nil {
		t.Fatal(err)
	}
	if entry != 4 || factor.Cmp(big.NewInt(2)) != 0 {
		t.Fatal("in-place decomposition changed the canonical data")
	}

	// No shallow big.Int copies are used: only direct pointer aliases are admitted.
	for _, field := range []string{"Seed", "Fixed"} {
		var certificate Certificate
		seed := &certificate.Seed
		if field == "Fixed" {
			seed = &certificate.Fixed
		}
		seed.SetInt64(1250)
		if err := m.BuildCertificateInto(&certificate, seed, &workspace); err != nil {
			t.Fatal(err)
		}
		if certificate.Seed.Cmp(big.NewInt(1250)) != 0 {
			t.Fatalf("building from %s changed the seed", field)
		}
		if certificate.Fixed.Cmp(big.NewInt(2)) != 0 || certificate.EntryTime != 4 {
			t.Fatalf("building from %s changed the canonical data", field)
		}
		if err := m.VerifyCertificate(&certificate, &workspace); err != nil {
			t.Fatal(err)
		}
	}
}

// TestVerificationNonmutation snapshots every field on both acceptance and rejection.
func TestVerificationNonmutation(t *testing.T) {
	m, err := NewMap(big.NewInt(5))
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	var certificate Certificate
	for alteration := 0; alteration <= 3; alteration++ {
		if err := m.BuildCertificateInto(&certificate, big.NewInt(1250), &workspace); err != nil {
			t.Fatal(err)
		}

		// Independently corrupt each field, retaining one valid control.
		switch alteration {
		case 1:
			certificate.Seed.Add(&certificate.Seed, big.NewInt(1))
		case 2:
			certificate.Fixed.Add(&certificate.Fixed, big.NewInt(1))
		case 3:
			certificate.EntryTime++
		}
		var seedBefore big.Int
		var fixedBefore big.Int
		seedBefore.Set(&certificate.Seed)
		fixedBefore.Set(&certificate.Fixed)
		timeBefore := certificate.EntryTime
		err := m.VerifyCertificate(&certificate, &workspace)
		if (err != nil) != (alteration != 0) {
			t.Fatalf("alteration %d returned %v", alteration, err)
		}
		if certificate.Seed.Cmp(&seedBefore) != 0 || certificate.Fixed.Cmp(&fixedBefore) != 0 {
			t.Fatalf("verification mutated an integer field for alteration %d", alteration)
		}
		if certificate.EntryTime != timeBefore {
			t.Fatalf("verification mutated entry time for alteration %d", alteration)
		}
	}
}
