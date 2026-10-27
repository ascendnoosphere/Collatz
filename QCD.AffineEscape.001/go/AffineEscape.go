// SPDX-License-Identifier: CC-BY-4.0

// Command AffineEscape verifies bounded instances of the gcd division barrier.
package main

import (
	"errors"
	"fmt"
	"math"
	"math/big"
)

// Parameters contains immutable positive raw-map coefficients.
type Parameters struct {
	Q big.Int
	C big.Int
	D big.Int
}

// Certificate records one exact initial division prefix and checked affine tail.
type Certificate struct {
	Seed             big.Int
	Anchor           big.Int
	FinalState       big.Int
	FormulaState     big.Int
	InitialDivisions uint64
	TailSteps        uint64
	CheckedStates    uint64
}

// Workspace owns reusable arithmetic buffers and must not be copied or shared concurrently.
type Workspace struct {
	Affine    big.Int
	Count     big.Int
	Divisor   big.Int
	Formula   big.Int
	GCD       big.Int
	Geom      big.Int
	One       big.Int
	Power     big.Int
	Remainder big.Int
	State     big.Int
	Temp      big.Int
}

// ParseParameters parses decimal coefficients and validates the positive theorem domain.
func ParseParameters(q, c, d string) (Parameters, error) {
	var p Parameters
	values := []struct {
		text string
		out  *big.Int
	}{
		{q, &p.Q},
		{c, &p.C},
		{d, &p.D},
	}
	for _, value := range values {
		if _, ok := value.out.SetString(value.text, 10); !ok {
			return Parameters{}, fmt.Errorf("invalid decimal integer %q", value.text)
		}
	}
	if err := ValidateParameters(&p); err != nil {
		return Parameters{}, err
	}
	return p, nil
}

// ValidateParameters enforces q at least two, positive c, and d at least two.
func ValidateParameters(p *Parameters) error {
	if p == nil {
		return errors.New("parameters are required")
	}
	var two big.Int
	two.SetInt64(2)
	if p.Q.Cmp(&two) < 0 {
		return errors.New("Q must be at least two")
	}
	if p.C.Sign() <= 0 {
		return errors.New("C must be positive")
	}
	if p.D.Cmp(&two) < 0 {
		return errors.New("D must be at least two")
	}
	return nil
}

// HasGCDBarrier decides whether gcd(Q,D) fails to divide C.
func HasGCDBarrier(p *Parameters, w *Workspace) (bool, error) {
	if err := ValidateParameters(p); err != nil {
		return false, err
	}
	if w == nil {
		return false, errors.New("workspace is required")
	}
	w.GCD.GCD(nil, nil, &p.Q, &p.D)
	w.Remainder.Mod(&p.C, &w.GCD)
	return w.Remainder.Sign() != 0, nil
}

// RawStepValidated computes one alias-safe instruction after validation.
func RawStepValidated(dst, n *big.Int, p *Parameters, w *Workspace) {
	w.Remainder.Mod(n, &p.D)
	if w.Remainder.Sign() == 0 {
		dst.Quo(n, &p.D)
		return
	}
	w.Affine.Mul(&p.Q, n)
	dst.Add(&w.Affine, &p.C)
}

// RawStep computes one positive raw-map instruction with alias-safe state output.
func RawStep(dst, n *big.Int, p *Parameters, w *Workspace) error {
	if dst == nil || n == nil || w == nil {
		return errors.New("destination, state, and workspace are required")
	}
	if err := ValidateParameters(p); err != nil {
		return err
	}
	if n.Sign() <= 0 {
		return errors.New("the state must be positive")
	}
	RawStepValidated(dst, n, p, w)
	return nil
}

// StripInitialDivisions extracts the canonical D-free anchor from a positive seed.
func StripInitialDivisions(dst, seed *big.Int, p *Parameters, w *Workspace) (
	uint64,
	error,
) {
	if dst == nil || seed == nil || w == nil {
		return 0, errors.New("destination, seed, and workspace are required")
	}
	if err := ValidateParameters(p); err != nil {
		return 0, err
	}
	if seed.Sign() <= 0 {
		return 0, errors.New("the seed must be positive")
	}
	dst.Set(seed)
	var divisions uint64
	for {
		w.Remainder.Mod(dst, &p.D)
		if w.Remainder.Sign() != 0 {
			return divisions, nil
		}
		if divisions == math.MaxUint64 {
			return 0, errors.New("initial division count exceeds uint64")
		}
		dst.Quo(dst, &p.D)
		divisions++
	}
}

// AffineTailFormulaValidated evaluates the closed form after validation.
func AffineTailFormulaValidated(
	dst, anchor *big.Int,
	tailSteps uint64,
	p *Parameters,
	w *Workspace,
) {
	w.Count.SetUint64(tailSteps)
	w.Power.Exp(&p.Q, &w.Count, nil)
	w.One.SetInt64(1)
	w.Geom.Sub(&w.Power, &w.One)
	w.Divisor.Sub(&p.Q, &w.One)
	w.Geom.Quo(&w.Geom, &w.Divisor)
	w.Formula.Mul(&w.Power, anchor)
	w.Temp.Mul(&p.C, &w.Geom)
	dst.Add(&w.Formula, &w.Temp)
}

// AffineTailFormula computes Q^j*x+C*(Q^j-1)/(Q-1) exactly.
func AffineTailFormula(dst, anchor *big.Int, tailSteps uint64, p *Parameters, w *Workspace) error {
	if dst == nil || anchor == nil || w == nil {
		return errors.New("destination, anchor, and workspace are required")
	}
	if err := ValidateParameters(p); err != nil {
		return err
	}
	if anchor.Sign() <= 0 {
		return errors.New("the anchor must be positive")
	}
	AffineTailFormulaValidated(dst, anchor, tailSteps, p, w)
	return nil
}

// CheckEscape verifies a finite certificate implied by the universal Lean theorem.
func CheckEscape(p *Parameters, seed *big.Int, tailSteps uint64, w *Workspace) (
	Certificate,
	error,
) {
	if w == nil {
		return Certificate{}, errors.New("workspace is required")
	}
	if tailSteps == math.MaxUint64 {
		return Certificate{}, errors.New("tailSteps is too large for the checked-state count")
	}
	barrier, err := HasGCDBarrier(p, w)
	if err != nil {
		return Certificate{}, err
	}
	if !barrier {
		return Certificate{}, errors.New("gcd(Q,D) must not divide C")
	}
	divisions, err := StripInitialDivisions(&w.State, seed, p, w)
	if err != nil {
		return Certificate{}, err
	}
	var certificate Certificate
	certificate.Seed.Set(seed)
	certificate.Anchor.Set(&w.State)
	certificate.InitialDivisions = divisions
	certificate.TailSteps = tailSteps

	// Compare the raw orbit with a separately maintained affine recurrence.
	w.Formula.Set(&certificate.Anchor)
	for j := uint64(0); ; j++ {
		if w.State.Cmp(&w.Formula) != 0 {
			return Certificate{}, fmt.Errorf("tail formula failed at step %d", j)
		}
		w.Remainder.Mod(&w.State, &p.D)
		if w.Remainder.Sign() == 0 {
			return Certificate{}, fmt.Errorf("division barrier failed at step %d", j)
		}
		certificate.CheckedStates++
		if j == tailSteps {
			break
		}
		w.Temp.Mul(&p.Q, &w.Formula)
		w.Formula.Add(&w.Temp, &p.C)
		RawStepValidated(&w.State, &w.State, p, w)
	}
	certificate.FinalState.Set(&w.State)
	certificate.FormulaState.Set(&w.Formula)
	return certificate, nil
}

// RunChecks exercises representative barriers and prints an exact bounded total.
func RunChecks() error {
	controls := []struct {
		q    string
		c    string
		d    string
		seed string
	}{
		{"6", "1", "4", "64"},
		{"10", "3", "6", "486"},
		{"12", "5", "8", "4096"},
		{"21", "2", "14", "2744"},
	}
	var w Workspace
	var checked uint64
	for _, control := range controls {
		p, err := ParseParameters(control.q, control.c, control.d)
		if err != nil {
			return err
		}
		var seed big.Int
		if _, ok := seed.SetString(control.seed, 10); !ok {
			return errors.New("invalid embedded seed")
		}
		certificate, err := CheckEscape(&p, &seed, 24, &w)
		if err != nil {
			return err
		}
		checked += certificate.CheckedStates
	}
	fmt.Printf("verified %d exact gcd-barrier states across %d controls\n", checked, len(controls))
	return nil
}

// main reports whether all deterministic certificate checks succeeded.
func main() {
	if err := RunChecks(); err != nil {
		panic(err)
	}
}
