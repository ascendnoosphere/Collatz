// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// TestKnownCycle checks an exact three-state dependent homogeneous cycle.
func TestKnownCycle(t *testing.T) {
	m, err := NewMap(Parameters{Base: 3, U: 2, V: 1})
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	seed := big.NewInt(10)
	certificate, err := m.BuildCertificate(seed, &workspace)
	if err != nil {
		t.Fatal(err)
	}
	want := []int64{10, 90, 30}
	if certificate.Period != 3 || certificate.Transient != 0 {
		t.Fatalf("unexpected period/transient: %d/%d", certificate.Period,
			certificate.Transient)
	}
	for index, state := range certificate.Cycle {
		if state.Cmp(big.NewInt(want[index])) != 0 {
			t.Fatalf("state %d: got %s, want %d", index, state.String(), want[index])
		}
	}
}

// TestCompositeBaseFactor checks that base-free means not divisible by the whole composite base.
func TestCompositeBaseFactor(t *testing.T) {
	m, err := NewMap(Parameters{Base: 4, U: 1, V: 3})
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	seed := new(big.Int).Exp(big.NewInt(4), big.NewInt(9), nil)
	seed.Mul(seed, big.NewInt(2))
	certificate, err := m.BuildCertificate(seed, &workspace)
	if err != nil {
		t.Fatal(err)
	}
	if certificate.BaseFree.Cmp(big.NewInt(2)) != 0 ||
		certificate.InitialExponent != 9 || certificate.TailExponent >= 4 {
		t.Fatalf("unexpected decomposition: factor=%s exponent=%d tail=%d",
			certificate.BaseFree.String(), certificate.InitialExponent,
			certificate.TailExponent)
	}
	if err := m.VerifyCertificate(&certificate, &workspace); err != nil {
		t.Fatal(err)
	}
}

// TestExhaustiveCertificates checks decomposition, rotation, primitive return, and height.
func TestExhaustiveCertificates(t *testing.T) {
	var workspace Workspace
	var seed big.Int
	var factor big.Int
	cache, err := NewCache(16)
	if err != nil {
		t.Fatal(err)
	}
	for base := uint64(2); base <= 9; base++ {
		for u := uint64(1); u <= 8; u++ {
			for v := uint64(1); v <= 8; v++ {
				if GreatestCommonDivisor(u, v) != 1 {
					continue
				}
				m, err := NewMap(Parameters{Base: base, U: u, V: v})
				if err != nil {
					t.Fatal(err)
				}
				for n := uint64(1); n <= 300; n++ {
					seed.SetUint64(n)
					if buildErr := m.BuildCertificateInto(&cache.Built, &seed,
						&workspace); buildErr != nil {
						t.Fatalf("base=%d u=%d v=%d n=%d: %v", base, u, v, n,
							buildErr)
					}
					if verifyErr := m.VerifyCertificate(&cache.Built,
						&workspace); verifyErr != nil {
						t.Fatalf("base=%d u=%d v=%d n=%d: %v", base, u, v, n,
							verifyErr)
					}

					// Each cycle state has the fixed factor and follows the exponent update.
					exponent := cache.Built.TailExponent
					for index := range cache.Built.Cycle {
						state := &cache.Built.Cycle[index]
						gotExponent, decomposeErr := m.Decompose(&factor, state, &workspace)
						if decomposeErr != nil {
							t.Fatal(decomposeErr)
						}
						if factor.Cmp(&cache.Built.BaseFree) != 0 || gotExponent != exponent {
							t.Fatalf("cycle decomposition mismatch at index %d", index)
						}
						exponent = m.ExponentStep(exponent)
					}
					if exponent != cache.Built.TailExponent {
						t.Fatal("exponent cycle did not return")
					}
				}
			}
		}
	}
}

// TestCoefficientDependence checks q^V=D^U for exact arbitrary-precision coefficients.
func TestCoefficientDependence(t *testing.T) {
	m, err := NewMap(Parameters{Base: 7, U: 19, V: 23})
	if err != nil {
		t.Fatal(err)
	}
	var q, d big.Int
	m.Coefficients(&q, &d)
	left := new(big.Int).Exp(&q, new(big.Int).SetUint64(m.Parameters.V), nil)
	right := new(big.Int).Exp(&d, new(big.Int).SetUint64(m.Parameters.U), nil)
	if left.Cmp(right) != 0 || m.Period() != 42 {
		t.Fatal("coefficient relation or primitive period failed")
	}
}

// TestInPlaceStep checks the supported destination/state alias.
func TestInPlaceStep(t *testing.T) {
	m, err := NewMap(Parameters{Base: 2, U: 3, V: 2})
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	state := big.NewInt(7)
	if err := m.Step(state, state, &workspace); err != nil {
		t.Fatal(err)
	}
	if state.Cmp(big.NewInt(56)) != 0 {
		t.Fatalf("in-place affine step: got %s", state.String())
	}
	state.SetInt64(28)
	if err := m.Step(state, state, &workspace); err != nil {
		t.Fatal(err)
	}
	if state.Cmp(big.NewInt(7)) != 0 {
		t.Fatalf("in-place division step: got %s", state.String())
	}
}

// TestCertificateOwnership checks that inputs and workspace do not alias returned integers.
func TestCertificateOwnership(t *testing.T) {
	m, err := NewMap(Parameters{Base: 2, U: 5, V: 3})
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	seed := big.NewInt(96)
	certificate, err := m.BuildCertificate(seed, &workspace)
	if err != nil {
		t.Fatal(err)
	}
	seed.SetInt64(1)
	workspace.current.SetInt64(1)
	workspace.factor.SetInt64(1)
	workspace.height.SetInt64(1)
	if certificate.Seed.Cmp(big.NewInt(96)) != 0 {
		t.Fatal("certificate aliases seed or workspace")
	}
	if err := m.VerifyCertificate(&certificate, &workspace); err != nil {
		t.Fatal(err)
	}
}

// TestTamperedCertificate checks rejection of altered scalar, integer, and cycle fields.
func TestTamperedCertificate(t *testing.T) {
	m, err := NewMap(Parameters{Base: 5, U: 2, V: 3})
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	certificate, err := m.BuildCertificate(big.NewInt(1250), &workspace)
	if err != nil {
		t.Fatal(err)
	}
	certificate.Transient++
	if err := m.VerifyCertificate(&certificate, &workspace); err == nil {
		t.Fatal("accepted altered transient")
	}
	certificate.Transient--
	certificate.BaseFree.Add(&certificate.BaseFree, big.NewInt(1))
	if err := m.VerifyCertificate(&certificate, &workspace); err == nil {
		t.Fatal("accepted altered base-free factor")
	}
	certificate.BaseFree.Sub(&certificate.BaseFree, big.NewInt(1))
	certificate.Cycle[0].Add(&certificate.Cycle[0], big.NewInt(1))
	var alteredCycle big.Int
	alteredCycle.Set(&certificate.Cycle[0])
	if err := m.VerifyCertificate(&certificate, &workspace); err == nil {
		t.Fatal("accepted altered cycle")
	}
	if certificate.Cycle[0].Cmp(&alteredCycle) != 0 {
		t.Fatal("verification mutated the rejected certificate")
	}
}

// TestReusableCacheAllocations checks that the warmed bounded hot path allocates nothing.
func TestReusableCacheAllocations(t *testing.T) {
	m, err := NewMap(Parameters{Base: 8, U: 7, V: 6})
	if err != nil {
		t.Fatal(err)
	}
	cache, err := NewCache(14)
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	seed := big.NewInt(250)
	if err := m.BuildCertificateInto(&cache.Built, seed, &workspace); err != nil {
		t.Fatal(err)
	}
	if err := m.VerifyCertificate(&cache.Built, &workspace); err != nil {
		t.Fatal(err)
	}
	allocations := testing.AllocsPerRun(1000, func() {
		if err := m.BuildCertificateInto(&cache.Built, seed, &workspace); err != nil {
			panic(err)
		}
		if err := m.VerifyCertificate(&cache.Built, &workspace); err != nil {
			panic(err)
		}
	})
	if allocations != 0 {
		t.Fatalf("warmed hot path allocated %.2f objects per run", allocations)
	}
}

// TestInvalidInputs checks every public validation boundary.
func TestInvalidInputs(t *testing.T) {
	bad := []Parameters{
		{Base: 1, U: 1, V: 1},
		{Base: 2, U: 0, V: 1},
		{Base: 2, U: 1, V: 0},
		{Base: 2, U: 2, V: 4},
		{Base: 2, U: ^uint64(0), V: 1},
	}
	for _, parameters := range bad {
		if _, err := NewMap(parameters); err == nil {
			t.Fatalf("accepted invalid parameters: %+v", parameters)
		}
	}
	m, err := NewMap(Parameters{Base: 2, U: 1, V: 1})
	if err != nil {
		t.Fatal(err)
	}
	var workspace Workspace
	var state big.Int
	if err := m.Step(&state, &state, &workspace); err == nil {
		t.Fatal("accepted zero state")
	}
	if _, err := m.BuildCertificate(big.NewInt(-1), &workspace); err == nil {
		t.Fatal("accepted negative seed")
	}
	if err := m.VerifyCertificate(nil, &workspace); err == nil {
		t.Fatal("accepted nil certificate")
	}
	cache, err := NewCache(m.Period())
	if err != nil {
		t.Fatal(err)
	}
	if err := m.BuildCertificateInto(&cache.Built, big.NewInt(1),
		&workspace); err != nil {
		t.Fatal(err)
	}
	cycle := cache.Built.Cycle
	cache.Built.Cycle = cache.Built.Cycle[:1]
	if err := m.VerifyCertificate(&cache.Built, &workspace); err == nil {
		t.Fatal("accepted wrong certificate cycle length")
	}
	cache.Built.Cycle = cycle
	if _, err := NewCache(^uint64(0)); err == nil {
		t.Fatal("accepted overflowing cache period")
	}
	smallCache, err := NewCache(1)
	if err != nil {
		t.Fatal(err)
	}
	if err := m.BuildCertificateInto(&smallCache.Built, big.NewInt(1),
		&workspace); err == nil {
		t.Fatal("accepted undersized certificate cache")
	}
}
