// SPDX-License-Identifier: CC-BY-4.0

package main

import (
	"math"
	"math/big"
	"testing"
)

// bruteRelation searches a deliberately redundant rectangle for a test oracle.
func bruteRelation(p *Parameters, limit uint64) bool {
	var qPower, dPower big.Int
	qPower.SetInt64(1)
	for a := uint64(1); a <= limit; a++ {
		qPower.Mul(&qPower, &p.Q)
		dPower.SetInt64(1)
		for b := uint64(1); b <= limit; b++ {
			dPower.Mul(&dPower, &p.D)
			if qPower.Cmp(&dPower) == 0 {
				return true
			}
		}
	}
	return false
}

// referencePrefix evaluates the raw definition without production orbit helpers.
func referencePrefix(p *Parameters, seed *big.Int, steps uint64) (*big.Int, uint64, uint64) {
	state := new(big.Int).Set(seed)
	var remainder big.Int
	var affines, divisions uint64
	for j := uint64(0); j < steps; j++ {
		remainder.Mod(state, &p.D)
		if remainder.Sign() == 0 {
			state.Quo(state, &p.D)
			divisions++
		} else {
			state.Mul(&p.Q, state)
			affines++
		}
	}
	return state, affines, divisions
}

// TestDetectPowerRelationExhaustive compares the complete detector with brute force.
func TestDetectPowerRelationExhaustive(t *testing.T) {
	t.Parallel()
	var w Workspace
	var dependent uint64
	for q := int64(2); q <= 128; q++ {
		for d := int64(2); d <= 128; d++ {
			p := Parameters{Q: *big.NewInt(q), D: *big.NewInt(d)}
			relation, err := DetectPowerRelation(&p, &w)
			if err != nil {
				t.Fatal(err)
			}
			want := bruteRelation(&p, 8)
			if relation.Dependent != want {
				t.Fatalf("relation mismatch for Q=%d D=%d", q, d)
			}
			if relation.Dependent {
				dependent++
				qPower := new(big.Int).Exp(&p.Q, new(big.Int).SetUint64(relation.Affine), nil)
				dPower := new(big.Int).Exp(&p.D, new(big.Int).SetUint64(relation.Divide), nil)
				if qPower.Cmp(dPower) != 0 {
					t.Fatalf("false witness for Q=%d D=%d", q, d)
				}
			}
		}
	}
	if dependent != 195 {
		t.Fatalf("checked %d dependent pairs, want 195", dependent)
	}
}

// TestIndependentPrefixes checks exact bounded invariants over a parameter grid.
func TestIndependentPrefixes(t *testing.T) {
	t.Parallel()
	var w Workspace
	var certificates, states uint64
	for q := int64(2); q <= 32; q++ {
		for d := int64(2); d <= 32; d++ {
			p := Parameters{Q: *big.NewInt(q), D: *big.NewInt(d)}
			relation, err := DetectPowerRelation(&p, &w)
			if err != nil {
				t.Fatal(err)
			}
			if relation.Dependent {
				continue
			}
			for seedValue := int64(1); seedValue <= 30; seedValue++ {
				seed := big.NewInt(seedValue)
				certificate, err := CheckIndependentPrefix(&p, seed, 15, &w)
				if err != nil {
					t.Fatal(err)
				}
				wantState, wantAffines, wantDivisions := referencePrefix(&p, seed, 15)
				if certificate.FinalState.Cmp(wantState) != 0 ||
					certificate.AffineCount != wantAffines ||
					certificate.DivisionCount != wantDivisions {
					t.Fatalf("prefix mismatch for Q=%d D=%d seed=%d", q, d, seedValue)
				}
				if certificate.AffineCount+certificate.DivisionCount != 15 ||
					certificate.CheckedStates != 16 {
					t.Fatal("certificate clock accounting failed")
				}
				certificates++
				states += certificate.CheckedStates
			}
		}
	}
	if certificates != 27060 || states != 432960 {
		t.Fatalf("checked %d certificates and %d states", certificates, states)
	}
}

// TestLargeRelation checks the source-scale factor-free power certificate.
func TestLargeRelation(t *testing.T) {
	t.Parallel()
	var q, d big.Int
	q.Exp(big.NewInt(2), big.NewInt(100), nil)
	d.Exp(big.NewInt(2), big.NewInt(101), nil)
	var w Workspace
	relation, err := DetectPowerRelation(&Parameters{Q: q, D: d}, &w)
	if err != nil {
		t.Fatal(err)
	}
	if !relation.Dependent || relation.Affine != 101 || relation.Divide != 100 {
		t.Fatalf("unexpected large relation: %+v", relation)
	}
}

// TestAliasesAndOwnership checks in-place stepping and certificate ownership.
func TestAliasesAndOwnership(t *testing.T) {
	t.Parallel()
	p, err := ParseParameters("6", "4")
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	state := big.NewInt(12)
	if err := HomogeneousStep(state, state, &p, &w); err != nil {
		t.Fatal(err)
	}
	if state.Int64() != 3 {
		t.Fatalf("in-place division returned %s", state.String())
	}
	if err := HomogeneousStep(state, state, &p, &w); err != nil {
		t.Fatal(err)
	}
	if state.Int64() != 18 {
		t.Fatalf("in-place affine step returned %s", state.String())
	}
	seed := big.NewInt(7)
	certificate, err := CheckIndependentPrefix(&p, seed, 8, &w)
	if err != nil {
		t.Fatal(err)
	}
	ownedSeed := new(big.Int).Set(&certificate.Seed)
	ownedFinal := new(big.Int).Set(&certificate.FinalState)
	seed.SetInt64(-1)
	w.state.SetInt64(-1)
	if certificate.Seed.Cmp(ownedSeed) != 0 || certificate.FinalState.Cmp(ownedFinal) != 0 {
		t.Fatal("certificate aliases caller or workspace storage")
	}
}

// TestRejectedInputs checks every public domain and nil boundary.
func TestRejectedInputs(t *testing.T) {
	t.Parallel()
	for _, input := range [][2]string{
		{"1", "2"},
		{"2", "1"},
		{"bad", "2"},
		{"2", "bad"},
	} {
		if _, err := ParseParameters(input[0], input[1]); err == nil {
			t.Fatalf("accepted invalid parameters %v", input)
		}
	}
	independent, err := ParseParameters("6", "4")
	if err != nil {
		t.Fatal(err)
	}
	dependent, err := ParseParameters("4", "8")
	if err != nil {
		t.Fatal(err)
	}
	var w Workspace
	if _, err := DetectPowerRelation(nil, &w); err == nil {
		t.Fatal("accepted nil parameters")
	}
	if _, err := DetectPowerRelation(&independent, nil); err == nil {
		t.Fatal("accepted nil relation workspace")
	}
	if _, err := CheckIndependentPrefix(&dependent, big.NewInt(1), 4, &w); err == nil {
		t.Fatal("accepted dependent coefficients")
	}
	for _, seed := range []*big.Int{nil, big.NewInt(0), big.NewInt(-1)} {
		if _, err := CheckIndependentPrefix(&independent, seed, 4, &w); err == nil {
			t.Fatalf("accepted invalid seed %v", seed)
		}
	}
	if _, err := CheckIndependentPrefix(
		&independent,
		big.NewInt(1),
		math.MaxUint64,
		&w,
	); err == nil {
		t.Fatal("accepted an unrepresentable checked-state count")
	}
	if err := HomogeneousStep(nil, big.NewInt(1), &independent, &w); err == nil {
		t.Fatal("accepted nil destination")
	}
	if err := HomogeneousStep(big.NewInt(1), nil, &independent, &w); err == nil {
		t.Fatal("accepted nil state")
	}
	if err := HomogeneousStep(big.NewInt(1), big.NewInt(1), &independent, nil); err == nil {
		t.Fatal("accepted nil step workspace")
	}
	if err := HomogeneousStep(big.NewInt(1), big.NewInt(-1), &independent, &w); err == nil {
		t.Fatal("accepted a negative state")
	}
}
