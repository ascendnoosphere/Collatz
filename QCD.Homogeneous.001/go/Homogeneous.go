// SPDX-License-Identifier: CC-BY-4.0

// Command Homogeneous verifies exact certificates for the independent homogeneous case.
package main

import (
	"errors"
	"fmt"
	"math"
	"math/big"
)

// Parameters contains immutable positive homogeneous coefficients.
type Parameters struct {
	Q big.Int
	D big.Int
}

// Relation records a positive equality Q^Affine = D^Divide.
type Relation struct {
	Affine    uint64
	Divide    uint64
	Dependent bool
}

// Certificate records one exact bounded prefix of an independent orbit.
type Certificate struct {
	Seed          big.Int
	FinalState    big.Int
	AffineCount   uint64
	DivisionCount uint64
	CheckedStates uint64
}

// Workspace owns all reusable integers used by certificate checks.
type Workspace struct {
	state     big.Int
	remainder big.Int
	qPower    big.Int
	dPower    big.Int
	left      big.Int
	right     big.Int
	relationQ big.Int
	relationD big.Int
}

// ValidateParameters enforces the positive homogeneous theorem domain.
func ValidateParameters(p *Parameters) error {
	if p == nil {
		return errors.New("parameters are required")
	}
	if p.Q.Cmp(big.NewInt(2)) < 0 {
		return errors.New("Q must be at least two")
	}
	if p.D.Cmp(big.NewInt(2)) < 0 {
		return errors.New("D must be at least two")
	}
	return nil
}

// ParseParameters parses exact decimal coefficients and validates their domain.
func ParseParameters(qText, dText string) (Parameters, error) {
	var p Parameters
	if _, ok := p.Q.SetString(qText, 10); !ok {
		return Parameters{}, errors.New("invalid decimal Q")
	}
	if _, ok := p.D.SetString(dText, 10); !ok {
		return Parameters{}, errors.New("invalid decimal D")
	}
	if err := ValidateParameters(&p); err != nil {
		return Parameters{}, err
	}
	return p, nil
}

// DetectPowerRelation decides whether positive powers of Q and D coincide.
func DetectPowerRelation(p *Parameters, w *Workspace) (Relation, error) {
	if w == nil {
		return Relation{}, errors.New("workspace is required")
	}
	if err := ValidateParameters(p); err != nil {
		return Relation{}, err
	}
	maxAffine := uint64(p.D.BitLen())
	maxDivide := uint64(p.Q.BitLen())
	w.relationQ.Set(&p.Q)
	w.relationD.Set(&p.D)
	for affine, divide := uint64(1), uint64(1); affine <= maxAffine && divide <= maxDivide; {
		switch w.relationQ.Cmp(&w.relationD) {
		case -1:
			affine++
			if affine <= maxAffine {
				w.relationQ.Mul(&w.relationQ, &p.Q)
			}
		case 1:
			divide++
			if divide <= maxDivide {
				w.relationD.Mul(&w.relationD, &p.D)
			}
		default:
			return Relation{Affine: affine, Divide: divide, Dependent: true}, nil
		}
	}
	return Relation{}, nil
}

// HomogeneousStep applies one positive raw instruction and permits in-place use.
func HomogeneousStep(dst, state *big.Int, p *Parameters, w *Workspace) error {
	if dst == nil || state == nil || w == nil {
		return errors.New("destination, state, and workspace are required")
	}
	if err := ValidateParameters(p); err != nil {
		return err
	}
	if state.Sign() <= 0 {
		return errors.New("state must be positive")
	}
	w.remainder.Mod(state, &p.D)
	if w.remainder.Sign() == 0 {
		dst.Quo(state, &p.D)
	} else {
		dst.Mul(&p.Q, state)
	}
	return nil
}

// CheckIndependentPrefix verifies a bounded no-return and monomial certificate.
func CheckIndependentPrefix(p *Parameters, seed *big.Int, steps uint64, w *Workspace) (
	Certificate,
	error,
) {
	if w == nil {
		return Certificate{}, errors.New("workspace is required")
	}
	if steps == math.MaxUint64 {
		return Certificate{}, errors.New("steps is too large for the checked-state count")
	}
	relation, err := DetectPowerRelation(p, w)
	if err != nil {
		return Certificate{}, err
	}
	if relation.Dependent {
		return Certificate{}, fmt.Errorf(
			"coefficients are dependent: Q^%d = D^%d",
			relation.Affine,
			relation.Divide,
		)
	}
	if seed == nil || seed.Sign() <= 0 {
		return Certificate{}, errors.New("seed must be positive")
	}
	var certificate Certificate
	certificate.Seed.Set(seed)
	w.state.Set(seed)
	w.qPower.SetInt64(1)
	w.dPower.SetInt64(1)
	for j := uint64(0); ; j++ {
		w.left.Mul(&w.state, &w.dPower)
		w.right.Mul(seed, &w.qPower)
		if w.left.Cmp(&w.right) != 0 {
			return Certificate{}, fmt.Errorf("monomial invariant failed at step %d", j)
		}
		if j > 0 && w.state.Cmp(seed) == 0 {
			return Certificate{}, fmt.Errorf("unexpected return at step %d", j)
		}
		certificate.CheckedStates++
		if j == steps {
			break
		}
		w.remainder.Mod(&w.state, &p.D)
		if w.remainder.Sign() == 0 {
			w.state.Quo(&w.state, &p.D)
			w.dPower.Mul(&w.dPower, &p.D)
			certificate.DivisionCount++
		} else {
			w.state.Mul(&p.Q, &w.state)
			w.qPower.Mul(&w.qPower, &p.Q)
			certificate.AffineCount++
		}
	}
	certificate.FinalState.Set(&w.state)
	return certificate, nil
}

// RunChecks exercises independent prefixes and large dependent controls.
func RunChecks() error {
	controls := []struct {
		q     string
		d     string
		seed  string
		steps uint64
	}{
		{"6", "4", "1", 40},
		{"12", "8", "7", 40},
		{"18", "12", "25", 40},
		{"45", "28", "81", 40},
	}
	var w Workspace
	var checked uint64
	for _, control := range controls {
		p, err := ParseParameters(control.q, control.d)
		if err != nil {
			return err
		}
		var seed big.Int
		if _, ok := seed.SetString(control.seed, 10); !ok {
			return errors.New("invalid embedded seed")
		}
		certificate, err := CheckIndependentPrefix(&p, &seed, control.steps, &w)
		if err != nil {
			return err
		}
		checked += certificate.CheckedStates
	}
	var q, d big.Int
	q.Exp(big.NewInt(2), big.NewInt(100), nil)
	d.Exp(big.NewInt(2), big.NewInt(101), nil)
	relation, err := DetectPowerRelation(&Parameters{Q: q, D: d}, &w)
	if err != nil {
		return err
	}
	if !relation.Dependent || relation.Affine != 101 || relation.Divide != 100 {
		return errors.New("large dependent control returned the wrong relation")
	}
	fmt.Printf("verified %d exact independent states and one large power relation\n", checked)
	return nil
}

// main reports whether every deterministic certificate check succeeded.
func main() {
	if err := RunChecks(); err != nil {
		panic(err)
	}
}
