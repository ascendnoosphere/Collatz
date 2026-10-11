// SPDX-License-Identifier: CC-BY-4.0
// Exact entry into the offset lattice and subsequent unit-offset normalization.
package main

import (
	"errors"
	"fmt"
	"math/big"
	"os"
)

// Parameters retains signed q,c,d and a nonnegative power witness k.
// Fields remain read-only during evaluation and do not alias workspace buffers.
type Parameters struct {
	Q big.Int
	C big.Int
	D big.Int
	K big.Int
}

// Certificate records the exact first entry, raw time and number of affine events.
// Fields are independently owned and do not alias parameters or workspace buffers.
type Certificate struct {
	Entry        big.Int
	Normalized   big.Int
	Steps        big.Int
	AffineEvents big.Int
}

// Workspace is exclusive and must not be copied after use or aliased with caller data.
// Its buffers are reused; math/big may allocate limbs and internal arithmetic work.
type Workspace struct {
	current   big.Int
	next      big.Int
	remainder big.Int
	gcd       big.Int
	power     big.Int
	magnitude big.Int
	steps     big.Int
	affine    big.Int
	one       big.Int
}

// ValidateParameters checks every hypothesis used by the terminating entry theorem.
func ValidateParameters(p *Parameters, w *Workspace) error {
	w.magnitude.Abs(&p.D)
	w.one.SetInt64(1)
	if w.magnitude.Cmp(big.NewInt(2)) < 0 {
		return errors.New("raw divisor must have magnitude at least two")
	}
	if p.C.Sign() == 0 || p.K.Sign() < 0 {
		return errors.New("offset must be nonzero and power witness nonnegative")
	}
	w.gcd.GCD(nil, nil, &p.C, &p.D)
	if w.gcd.Cmp(&w.one) != 0 {
		return errors.New("offset and divisor must be coprime")
	}
	w.power.Exp(&p.Q, &p.K, nil)
	w.remainder.Rem(&w.power, &p.C)
	if w.remainder.Sign() != 0 {
		return errors.New("offset does not divide the witnessed multiplier power")
	}
	return nil
}

// ParseParameters rejects malformed data and validates the complete arithmetic witness.
func ParseParameters(q, c, d, k string) (Parameters, error) {
	var p Parameters
	values := []struct {
		text string
		out  *big.Int
	}{{q, &p.Q}, {c, &p.C}, {d, &p.D}, {k, &p.K}}
	for _, value := range values {
		if _, ok := value.out.SetString(value.text, 10); !ok {
			return Parameters{}, fmt.Errorf("invalid integer parameter: %q", value.text)
		}
	}
	var w Workspace
	if err := ValidateParameters(&p, &w); err != nil {
		return Parameters{}, err
	}
	return p, nil
}

// RawStep preserves the signed divisor and applies division before the affine branch.
func RawStep(p *Parameters, n, out *big.Int, w *Workspace) bool {
	w.remainder.Rem(n, &p.D)
	affine := w.remainder.Sign() != 0
	if affine {
		w.next.Mul(&p.Q, n)
		w.next.Add(&w.next, &p.C)
	} else {
		w.next.Quo(n, &p.D)
	}
	out.Set(&w.next)
	return affine
}

// Capture terminates by the lexicographic rank (remaining affine budget, |current state|).
// Each loop checks entry before taking another exact raw step; outputs are caller-owned.
func Capture(p *Parameters, n *big.Int, out *Certificate, w *Workspace) error {
	if err := ValidateParameters(p, w); err != nil {
		return err
	}
	w.current.Set(n)
	w.steps.SetInt64(0)
	w.affine.SetInt64(0)
	for {
		w.remainder.Rem(&w.current, &p.C)
		if w.remainder.Sign() == 0 {
			break
		}
		if RawStep(p, &w.current, &w.current, w) {
			w.affine.Add(&w.affine, &w.one)
			if w.affine.Cmp(&p.K) > 0 {
				return errors.New("affine-event budget violated")
			}
		}
		w.steps.Add(&w.steps, &w.one)
	}
	out.Entry.Set(&w.current)
	out.Normalized.Quo(&w.current, &p.C)
	out.Steps.Set(&w.steps)
	out.AffineEvents.Set(&w.affine)
	return nil
}

// CheckTail compares an exact finite tail with the corresponding unit-offset raw trajectory.
func CheckTail(p *Parameters, certificate *Certificate, length int) error {
	if length < 0 {
		return errors.New("tail length must be nonnegative")
	}
	var originalWorkspace, unitWorkspace Workspace
	if err := ValidateParameters(p, &originalWorkspace); err != nil {
		return err
	}
	var unit Parameters
	unit.Q.Set(&p.Q)
	unit.C.SetInt64(1)
	unit.D.Set(&p.D)
	var original, normalized, scaled big.Int
	original.Set(&certificate.Entry)
	normalized.Set(&certificate.Normalized)
	scaled.Mul(&p.C, &normalized)
	if scaled.Cmp(&original) != 0 {
		return errors.New("entry is not the claimed scaled integer")
	}
	// Checking time zero separately keeps the loop counter safe even at the largest int.
	for i := 0; i < length; i++ {
		RawStep(p, &original, &original, &originalWorkspace)
		RawStep(&unit, &normalized, &normalized, &unitWorkspace)
		scaled.Mul(&p.C, &normalized)
		if scaled.Cmp(&original) != 0 {
			return errors.New("unit-offset tail disagrees with the original raw clock")
		}
	}
	return nil
}

// RunChecks computes exact entry certificates for positive, signed and zero-multiplier controls.
func RunChecks() error {
	controls := []struct {
		q, c, d, k, seed string
		steps, events    int64
		entry, unit      int64
	}{
		{"3", "9", "2", "2", "1", 4, 2, 18, 2},
		{"2", "8", "3", "3", "1", 3, 3, 64, 8},
		{"3", "-9", "-2", "2", "-1", 4, 2, -18, 2},
		{"0", "10", "-3", "1", "9", 3, 1, 10, 1},
	}
	var w Workspace
	var seed big.Int
	var certificate Certificate
	for _, control := range controls {
		p, err := ParseParameters(control.q, control.c, control.d, control.k)
		if err != nil {
			return err
		}
		seed.SetString(control.seed, 10)
		if err := Capture(&p, &seed, &certificate, &w); err != nil {
			return err
		}
		if !certificate.Steps.IsInt64() || certificate.Steps.Int64() != control.steps ||
			!certificate.AffineEvents.IsInt64() || certificate.AffineEvents.Int64() != control.events ||
			!certificate.Entry.IsInt64() || certificate.Entry.Int64() != control.entry ||
			!certificate.Normalized.IsInt64() || certificate.Normalized.Int64() != control.unit {
			return fmt.Errorf("incorrect entry certificate for (%s,%s,%s)",
				control.q, control.c, control.d)
		}
		if err := CheckTail(&p, &certificate, 16); err != nil {
			return err
		}
		fmt.Printf("(%s,%s,%s): seed=%s, time=%s, affine=%s, entry=%s, normalized=%s\n",
			control.q, control.c, control.d, control.seed, certificate.Steps.String(),
			certificate.AffineEvents.String(), certificate.Entry.String(),
			certificate.Normalized.String())
	}
	return nil
}

// main is the Makefile entry point for the exact normalization controls.
func main() {
	if err := RunChecks(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
