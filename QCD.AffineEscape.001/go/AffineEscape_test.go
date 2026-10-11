// SPDX-License-Identifier: CC-BY-4.0

package main

import (
	"math"
	"math/big"
	"testing"
)

// referenceStep computes the raw map without using production arithmetic buffers.
func referenceStep(n, q, c, d *big.Int) *big.Int {
	remainder := new(big.Int).Mod(new(big.Int).Set(n), d)
	if remainder.Sign() == 0 {
		return new(big.Int).Quo(new(big.Int).Set(n), d)
	}
	return new(big.Int).Add(new(big.Int).Mul(q, n), c)
}

// referenceCertificate follows the raw map through the initial divisions and affine tail.
func referenceCertificate(seed *big.Int, tailSteps uint64, p *Parameters) (
	uint64,
	*big.Int,
	*big.Int,
) {
	state := new(big.Int).Set(seed)
	var divisions uint64
	for new(big.Int).Mod(new(big.Int).Set(state), &p.D).Sign() == 0 {
		state = referenceStep(state, &p.Q, &p.C, &p.D)
		divisions++
	}
	anchor := new(big.Int).Set(state)
	for j := uint64(0); j < tailSteps; j++ {
		state = referenceStep(state, &p.Q, &p.C, &p.D)
	}
	return divisions, anchor, state
}

// referenceFormula evaluates the affine tail without production helpers.
func referenceFormula(anchor *big.Int, tailSteps uint64, p *Parameters) *big.Int {
	exponent := new(big.Int).SetUint64(tailSteps)
	power := new(big.Int).Exp(&p.Q, exponent, nil)
	geometric := new(big.Int).Sub(new(big.Int).Set(power), big.NewInt(1))
	geometric.Quo(geometric, new(big.Int).Sub(new(big.Int).Set(&p.Q), big.NewInt(1)))
	return new(big.Int).Add(
		new(big.Int).Mul(power, anchor),
		new(big.Int).Mul(&p.C, geometric),
	)
}

// TestExhaustiveSmallBarriers checks every bounded theorem instance and exact count.
func TestExhaustiveSmallBarriers(t *testing.T) {
	var w Workspace
	var certificates uint64
	var states uint64
	for q := int64(2); q <= 12; q++ {
		for c := int64(1); c <= 12; c++ {
			for d := int64(2); d <= 12; d++ {
				p, err := ParseParameters(
					big.NewInt(q).String(),
					big.NewInt(c).String(),
					big.NewInt(d).String(),
				)
				if err != nil {
					t.Fatal(err)
				}
				barrier, err := HasGCDBarrier(&p, &w)
				if err != nil {
					t.Fatal(err)
				}
				if !barrier {
					continue
				}
				for seedValue := int64(1); seedValue <= 40; seedValue++ {
					seed := big.NewInt(seedValue)
					certificate, err := CheckEscape(&p, seed, 12, &w)
					if err != nil {
						t.Fatalf("q=%d c=%d d=%d seed=%d: %v", q, c, d, seedValue, err)
					}
					wantDivisions, wantAnchor, wantFinal :=
						referenceCertificate(seed, 12, &p)
					wantFormula := referenceFormula(wantAnchor, 12, &p)
					if certificate.InitialDivisions != wantDivisions ||
						certificate.Anchor.Cmp(wantAnchor) != 0 ||
						certificate.FinalState.Cmp(wantFinal) != 0 ||
						certificate.FormulaState.Cmp(wantFormula) != 0 {
						t.Fatalf("certificate mismatch at q=%d c=%d d=%d seed=%d",
							q, c, d, seedValue)
					}
					certificates++
					states += certificate.CheckedStates
				}
			}
		}
	}
	if certificates != 16600 || states != 215800 {
		t.Fatalf("checked %d certificates and %d states", certificates, states)
	}
}

// TestKnownControl checks the displayed finite prefix independently.
func TestKnownControl(t *testing.T) {
	p, err := ParseParameters("6", "1", "4")
	if err != nil {
		t.Fatal(err)
	}
	seed := big.NewInt(64)
	var w Workspace
	certificate, err := CheckEscape(&p, seed, 4, &w)
	if err != nil {
		t.Fatal(err)
	}
	if certificate.InitialDivisions != 3 || certificate.Anchor.Int64() != 1 ||
		certificate.FinalState.Int64() != 1555 || certificate.CheckedStates != 5 {
		t.Fatalf("unexpected control certificate: %+v", certificate)
	}
}

// TestLargeIntegers checks a 200-bit multiplier and a long exact division prefix.
func TestLargeIntegers(t *testing.T) {
	q := new(big.Int).Lsh(big.NewInt(1), 200)
	q.Add(q, big.NewInt(2))
	d := new(big.Int).Lsh(big.NewInt(1), 128)
	p, err := ParseParameters(q.String(), "3", d.String())
	if err != nil {
		t.Fatal(err)
	}
	seed := new(big.Int).Exp(d, big.NewInt(4), nil)
	seed.Mul(seed, big.NewInt(12345))
	var w Workspace
	certificate, err := CheckEscape(&p, seed, 7, &w)
	if err != nil {
		t.Fatal(err)
	}
	wantDivisions, wantAnchor, wantFinal := referenceCertificate(seed, 7, &p)
	if wantDivisions != 4 || certificate.InitialDivisions != wantDivisions ||
		certificate.Anchor.Cmp(wantAnchor) != 0 || certificate.FinalState.Cmp(wantFinal) != 0 {
		t.Fatal("large-integer certificate mismatch")
	}
}

// TestAliasesAndOwnership checks in-place operations and returned-value ownership.
func TestAliasesAndOwnership(t *testing.T) {
	p, err := ParseParameters("6", "1", "4")
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	state := big.NewInt(7)
	if err := RawStep(state, state, &p, &w); err != nil {
		t.Fatal(err)
	}
	if state.Int64() != 43 {
		t.Fatalf("in-place step returned %s", state.String())
	}
	state.SetInt64(64)
	divisions, err := StripInitialDivisions(state, state, &p, &w)
	if err != nil || divisions != 3 || state.Int64() != 1 {
		t.Fatalf("in-place division strip returned %s after %d divisions: %v",
			state.String(), divisions, err)
	}
	if err := AffineTailFormula(state, state, 3, &p, &w); err != nil {
		t.Fatal(err)
	}
	if state.Int64() != 259 {
		t.Fatalf("in-place formula returned %s", state.String())
	}

	seed := big.NewInt(64)
	certificate, err := CheckEscape(&p, seed, 3, &w)
	if err != nil {
		t.Fatal(err)
	}
	ownedSeed := new(big.Int).Set(&certificate.Seed)
	ownedAnchor := new(big.Int).Set(&certificate.Anchor)
	ownedFinal := new(big.Int).Set(&certificate.FinalState)
	ownedFormula := new(big.Int).Set(&certificate.FormulaState)
	seed.SetInt64(-1)
	w.State.SetInt64(-1)
	w.Formula.SetInt64(-1)
	if certificate.Seed.Cmp(ownedSeed) != 0 || certificate.Anchor.Cmp(ownedAnchor) != 0 ||
		certificate.FinalState.Cmp(ownedFinal) != 0 ||
		certificate.FormulaState.Cmp(ownedFormula) != 0 {
		t.Fatal("certificate aliases caller or workspace storage")
	}
}

// TestRejectedInputs checks theorem boundaries and API failures.
func TestRejectedInputs(t *testing.T) {
	for _, values := range [][3]string{
		{"1", "1", "2"},
		{"2", "0", "2"},
		{"2", "1", "1"},
		{"bad", "1", "2"},
		{"2", "bad", "2"},
		{"2", "1", "bad"},
	} {
		if _, err := ParseParameters(values[0], values[1], values[2]); err == nil {
			t.Fatalf("accepted invalid parameters %v", values)
		}
	}
	p, err := ParseParameters("6", "2", "4")
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	if _, err := CheckEscape(&p, big.NewInt(1), 3, &w); err == nil {
		t.Fatal("accepted a cell without the gcd barrier")
	}
	barrier, err := ParseParameters("6", "1", "4")
	if err != nil {
		t.Fatal(err)
	}
	for _, seed := range []*big.Int{big.NewInt(0), big.NewInt(-1), nil} {
		if _, err := CheckEscape(&barrier, seed, 3, &w); err == nil {
			t.Fatalf("accepted invalid seed %v", seed)
		}
	}
	if _, err := CheckEscape(&barrier, big.NewInt(1), math.MaxUint64, &w); err == nil {
		t.Fatal("accepted an unrepresentable checked-state count")
	}
	if _, err := CheckEscape(nil, big.NewInt(1), 3, &w); err == nil {
		t.Fatal("accepted nil parameters")
	}
	if _, err := HasGCDBarrier(&barrier, nil); err == nil {
		t.Fatal("accepted a nil workspace")
	}
	if err := RawStep(nil, big.NewInt(1), &barrier, &w); err == nil {
		t.Fatal("accepted a nil destination")
	}
	if err := RawStep(big.NewInt(1), nil, &barrier, &w); err == nil {
		t.Fatal("accepted a nil raw state")
	}
	if err := RawStep(big.NewInt(1), big.NewInt(1), &barrier, nil); err == nil {
		t.Fatal("accepted a nil raw-step workspace")
	}
	if _, err := StripInitialDivisions(nil, big.NewInt(1), &barrier, &w); err == nil {
		t.Fatal("accepted a nil division-strip destination")
	}
	if _, err := StripInitialDivisions(big.NewInt(1), nil, &barrier, &w); err == nil {
		t.Fatal("accepted a nil division-strip seed")
	}
	if err := AffineTailFormula(nil, big.NewInt(1), 1, &barrier, &w); err == nil {
		t.Fatal("accepted a nil formula destination")
	}
	if err := AffineTailFormula(big.NewInt(1), big.NewInt(-1), 1, &barrier, &w); err == nil {
		t.Fatal("accepted a negative formula anchor")
	}
}
