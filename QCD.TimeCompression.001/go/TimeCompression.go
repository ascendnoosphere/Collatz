// SPDX-License-Identifier: CC-BY-4.0

// Command TimeCompression verifies exact common-divisor-power block expansion.
package main

import (
	"errors"
	"fmt"
	"math"
	"math/big"
)

// Parameters contains immutable original and compressed coefficients.
type Parameters struct {
	Q           big.Int
	C           big.Int
	D           big.Int
	CompressedQ big.Int
	CompressedC big.Int
	A           uint64
}

// Certificate records one checked compressed prefix and its expanded raw time.
type Certificate struct {
	Endpoint        big.Int
	RawSteps        big.Int
	CompressedSteps uint64
	AffineEvents    uint64
}

// Workspace owns reusable arithmetic buffers and must not be copied or shared concurrently.
type Workspace struct {
	AbsD       big.Int
	Boundary   big.Int
	Check      big.Int
	Compressed big.Int
	Exponent   big.Int
	Factor     big.Int
	Original   big.Int
	Product    big.Int
	Quotient   big.Int
	RawTotal   big.Int
	Remainder  big.Int
	State      big.Int
	Step       big.Int
	Two        big.Int
}

// ParseParameters parses decimal coefficients and validates the exact factorization.
func ParseParameters(q, c, d, compressedQ, compressedC string, a uint64) (
	Parameters,
	error,
) {
	var p Parameters
	values := []struct {
		text string
		out  *big.Int
	}{
		{q, &p.Q},
		{c, &p.C},
		{d, &p.D},
		{compressedQ, &p.CompressedQ},
		{compressedC, &p.CompressedC},
	}
	for _, value := range values {
		if _, ok := value.out.SetString(value.text, 10); !ok {
			return Parameters{}, fmt.Errorf("invalid decimal integer %q", value.text)
		}
	}
	p.A = a
	var w Workspace
	if err := ValidateParameters(&p, &w); err != nil {
		return Parameters{}, err
	}
	return p, nil
}

// ValidateParameters checks the divisor, clock range, and both coefficient identities.
func ValidateParameters(p *Parameters, w *Workspace) error {
	if p == nil || w == nil {
		return errors.New("parameters and workspace are required")
	}
	w.AbsD.Abs(&p.D)
	w.Two.SetInt64(2)
	if w.AbsD.Cmp(&w.Two) < 0 {
		return errors.New("the divisor must have absolute value at least two")
	}
	if p.A == math.MaxUint64 {
		return errors.New("the exponent must admit the affine block length A+1")
	}
	w.Exponent.SetUint64(p.A)
	w.Factor.Exp(&p.D, &w.Exponent, nil)
	w.Check.Mul(&w.Factor, &p.CompressedQ)
	if w.Check.Cmp(&p.Q) != 0 {
		return errors.New("Q is not D^A times the compressed multiplier")
	}
	w.Check.Mul(&w.Factor, &p.CompressedC)
	if w.Check.Cmp(&p.C) != 0 {
		return errors.New("C is not D^A times the compressed offset")
	}
	return nil
}

// RawStep applies one signed division-first raw step with caller-selected coefficients.
func RawStep(q, c, d, n, out *big.Int, w *Workspace) bool {
	w.Quotient.QuoRem(n, d, &w.Remainder)
	if w.Remainder.Sign() == 0 {
		out.Set(&w.Quotient)
		return false
	}
	w.Product.Mul(q, n)
	out.Add(&w.Product, c)
	return true
}

// AdvanceValidatedBlock expands a block after its immutable parameters have been checked.
func AdvanceValidatedBlock(p *Parameters, n, out *big.Int, w *Workspace) (
	uint64,
	bool,
	error,
) {
	if n == nil || out == nil {
		return 0, false, errors.New("input and output states are required")
	}
	w.State.Set(n)
	w.Quotient.QuoRem(&w.State, &p.D, &w.Remainder)
	if w.Remainder.Sign() == 0 {
		out.Set(&w.Quotient)
		return 1, false, nil
	}

	// The affine image carries the declared power and each following division is forced.
	w.Product.Mul(&p.Q, &w.State)
	w.State.Add(&w.Product, &p.C)
	for i := uint64(0); i < p.A; i++ {
		w.Quotient.QuoRem(&w.State, &p.D, &w.Remainder)
		if w.Remainder.Sign() != 0 {
			return 0, false, errors.New("declared affine block lost a forced division")
		}
		w.State.Set(&w.Quotient)
	}
	out.Set(&w.State)
	return p.A + 1, true, nil
}

// AdvanceBlock expands one compressed event into its exact original raw block.
func AdvanceBlock(p *Parameters, n, out *big.Int, w *Workspace) (
	uint64,
	bool,
	error,
) {
	if err := ValidateParameters(p, w); err != nil {
		return 0, false, err
	}
	return AdvanceValidatedBlock(p, n, out, w)
}

// CompressedStep applies one raw step with the divided affine coefficients.
func CompressedStep(p *Parameters, n, out *big.Int, w *Workspace) (bool, error) {
	if n == nil || out == nil {
		return false, errors.New("input and output states are required")
	}
	if err := ValidateParameters(p, w); err != nil {
		return false, err
	}
	return RawStep(&p.CompressedQ, &p.CompressedC, &p.D, n, out, w), nil
}

// CheckValidatedBlock compares one block after its immutable parameters have been checked.
func CheckValidatedBlock(p *Parameters, n *big.Int, w *Workspace) (uint64, bool, error) {
	if n == nil {
		return 0, false, errors.New("the boundary state is required")
	}
	w.Boundary.Set(n)
	steps, affine, err := AdvanceValidatedBlock(p, &w.Boundary, &w.Original, w)
	if err != nil {
		return 0, false, err
	}
	RawStep(&p.CompressedQ, &p.CompressedC, &p.D, &w.Boundary, &w.Compressed, w)
	if w.Original.Cmp(&w.Compressed) != 0 {
		return 0, false, errors.New("expanded and compressed endpoints differ")
	}
	return steps, affine, nil
}

// CheckBlock compares one original block with one compressed step at the same boundary.
func CheckBlock(p *Parameters, n *big.Int, w *Workspace) (uint64, bool, error) {
	if err := ValidateParameters(p, w); err != nil {
		return 0, false, err
	}
	return CheckValidatedBlock(p, n, w)
}

// CheckTrajectory checks every block of a compressed prefix and records the exact raw clock.
func CheckTrajectory(
	p *Parameters,
	n *big.Int,
	compressedSteps uint64,
	out *Certificate,
	w *Workspace,
) error {
	if n == nil || out == nil {
		return errors.New("input state and certificate are required")
	}
	if err := ValidateParameters(p, w); err != nil {
		return err
	}
	w.Boundary.Set(n)
	w.RawTotal.SetInt64(0)
	affineEvents := uint64(0)
	for i := uint64(0); i < compressedSteps; i++ {
		steps, affine, err := CheckValidatedBlock(p, &w.Boundary, w)
		if err != nil {
			return err
		}
		if affine {
			affineEvents++
		}
		w.Step.SetUint64(steps)
		w.RawTotal.Add(&w.RawTotal, &w.Step)
		w.Boundary.Set(&w.Compressed)
	}
	out.Endpoint.Set(&w.Boundary)
	out.RawSteps.Set(&w.RawTotal)
	out.CompressedSteps = compressedSteps
	out.AffineEvents = affineEvents
	return nil
}

// RunChecks verifies representative positive, signed, divisible, and zero-multiplier blocks.
func RunChecks() error {
	controls := []struct {
		q           string
		c           string
		d           string
		compressedQ string
		compressedC string
		a           uint64
		seed        string
		steps       uint64
	}{
		{"4", "4", "2", "1", "1", 2, "1", 1},
		{"-6", "3", "-3", "2", "-1", 1, "2", 1},
		{"0", "40", "2", "0", "5", 3, "3", 1},
		{"100", "-25", "5", "4", "-1", 2, "25", 1},
	}
	for _, control := range controls {
		p, err := ParseParameters(
			control.q,
			control.c,
			control.d,
			control.compressedQ,
			control.compressedC,
			control.a,
		)
		if err != nil {
			return err
		}
		seed, ok := new(big.Int).SetString(control.seed, 10)
		if !ok {
			return errors.New("invalid control seed")
		}
		var certificate Certificate
		var w Workspace
		if err := CheckTrajectory(&p, seed, control.steps, &certificate, &w); err != nil {
			return err
		}
		fmt.Printf(
			"D=%s A=%d seed=%s compressed=%d affine=%d raw=%s endpoint=%s\n",
			control.d,
			control.a,
			control.seed,
			certificate.CompressedSteps,
			certificate.AffineEvents,
			certificate.RawSteps.String(),
			certificate.Endpoint.String(),
		)
	}
	return nil
}

// main runs the exact arithmetic controls.
func main() {
	if err := RunChecks(); err != nil {
		panic(err)
	}
}
