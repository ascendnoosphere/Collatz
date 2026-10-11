// SPDX-License-Identifier: CC-BY-4.0
// Exact arithmetic counterparts of GuardedDynamics, GuardedRecovery and AffineWords.
package main

import (
	"errors"
	"fmt"
	"math/big"
	"os"
)

// Parameters has |D| >= 2; its signed fields remain read-only during evaluation.
type Parameters struct {
	Q big.Int
	C big.Int
	D big.Int
}

// Letter distinguishes raw affine events from raw exact divisions.
type Letter uint8

const (
	Affine Letter = iota
	Divide
)

// AffineData represents (P*x+B)/Q; B is the full offset, including the additive parameter.
type AffineData struct {
	P big.Int
	B big.Int
	Q big.Int
}

// Workspace reuses buffers; math/big may still allocate limbs or internal arithmetic work.
// Do not copy a used workspace, share it concurrently, or alias its buffers with caller data.
type Workspace struct {
	current     big.Int
	next        big.Int
	remainder   big.Int
	product     big.Int
	offset      big.Int
	denominator big.Int
	term        big.Int
	exponent    big.Int
	delta       big.Int
	gcd         big.Int
	multiplier  big.Rat
	translation big.Rat
	divisor     big.Rat
}

// ParseParameters rejects invalid signed divisors without restricting the affine parameters.
func ParseParameters(q, c, d string) (Parameters, error) {
	var p Parameters
	values := []struct {
		text string
		out  *big.Int
	}{{q, &p.Q}, {c, &p.C}, {d, &p.D}}
	for _, value := range values {
		if _, ok := value.out.SetString(value.text, 10); !ok {
			return Parameters{}, fmt.Errorf("invalid integer parameter: %q", value.text)
		}
	}
	var magnitude big.Int
	magnitude.Abs(&p.D)
	if magnitude.Cmp(big.NewInt(2)) < 0 {
		return Parameters{}, errors.New("raw divisor must have magnitude at least two")
	}
	return p, nil
}

// RawStep uses division precedence and exact signed division, including at zero.
func RawStep(p *Parameters, n, out *big.Int, w *Workspace) {
	w.remainder.Rem(n, &p.D)
	if w.remainder.Sign() == 0 {
		w.next.Quo(n, &p.D)
	} else {
		w.next.Mul(&p.Q, n)
		w.next.Add(&w.next, &p.C)
	}
	out.Set(&w.next)
}

// ExecuteWord rejects every illegal intermediate instruction and leaves out unchanged on failure.
func ExecuteWord(p *Parameters, word []Letter, n, out *big.Int, w *Workspace) bool {
	w.current.Set(n)
	for _, letter := range word {
		w.remainder.Rem(&w.current, &p.D)
		divisible := w.remainder.Sign() == 0
		switch letter {
		case Affine:
			if divisible {
				return false
			}
			w.next.Mul(&w.current, &p.Q)
			w.next.Add(&w.next, &p.C)
			w.current.Set(&w.next)
		case Divide:
			if !divisible {
				return false
			}
			w.current.Quo(&w.current, &p.D)
		default:
			return false
		}
	}
	out.Set(&w.current)
	return true
}

// RawTrace fills a caller-owned word buffer and retains its exact raw endpoint.
func RawTrace(p *Parameters, word []Letter, n, out *big.Int, w *Workspace) {
	word = word[:len(word)]
	w.current.Set(n)
	for i := range word {
		w.remainder.Rem(&w.current, &p.D)
		if w.remainder.Sign() == 0 {
			word[i] = Divide
		} else {
			word[i] = Affine
		}
		RawStep(p, &w.current, &w.current, w)
	}
	out.Set(&w.current)
}

// EmptyAffine initializes the unreduced identity data in a caller-owned object.
func EmptyAffine(out *AffineData) {
	out.P.SetInt64(1)
	out.B.SetInt64(0)
	out.Q.SetInt64(1)
}

// AffineThen executes first and then second; out may alias either input but not workspace buffers.
func AffineThen(first, second, out *AffineData, w *Workspace) error {
	if first.Q.Sign() == 0 || second.Q.Sign() == 0 {
		return errors.New("affine presentation has a zero denominator")
	}
	w.product.Mul(&second.P, &first.P)
	w.offset.Mul(&second.P, &first.B)
	w.term.Mul(&second.B, &first.Q)
	w.offset.Add(&w.offset, &w.term)
	w.denominator.Mul(&second.Q, &first.Q)
	out.P.Set(&w.product)
	out.B.Set(&w.offset)
	out.Q.Set(&w.denominator)
	return nil
}

// RawWordAffine computes the rational relaxation without claiming the raw word is legal.
func RawWordAffine(p *Parameters, word []Letter, out *AffineData, w *Workspace) error {
	EmptyAffine(out)
	for _, letter := range word {
		switch letter {
		case Affine:
			w.product.Mul(&p.Q, &out.P)
			w.offset.Mul(&p.Q, &out.B)
			w.term.Mul(&p.C, &out.Q)
			w.offset.Add(&w.offset, &w.term)
			out.P.Set(&w.product)
			out.B.Set(&w.offset)
		case Divide:
			w.denominator.Mul(&out.Q, &p.D)
			out.Q.Set(&w.denominator)
		default:
			return errors.New("unknown raw instruction")
		}
	}
	return nil
}

// ExponentWord keeps zero exponents as algebraic letters, not accelerated-itinerary certificates.
func ExponentWord(p *Parameters, word []uint64, out *AffineData, w *Workspace) {
	EmptyAffine(out)
	for _, exponent := range word {
		w.exponent.SetUint64(exponent)
		w.denominator.Exp(&p.D, &w.exponent, nil)
		w.product.Mul(&p.Q, &out.P)
		w.offset.Mul(&p.Q, &out.B)
		w.term.Mul(&p.C, &out.Q)
		w.offset.Add(&w.offset, &w.term)
		out.P.Set(&w.product)
		out.B.Set(&w.offset)
		w.term.Mul(&out.Q, &w.denominator)
		out.Q.Set(&w.term)
	}
}

// RationalAction evaluates an affine relaxation exactly, with no floating-point conversion.
func RationalAction(a *AffineData, x *big.Rat, out *big.Rat, w *Workspace) error {
	if a.Q.Sign() == 0 {
		return errors.New("affine presentation has a zero denominator")
	}
	w.multiplier.SetInt(&a.P)
	w.translation.SetInt(&a.B)
	w.divisor.SetInt(&a.Q)
	out.Mul(&w.multiplier, x)
	out.Add(out, &w.translation)
	out.Quo(out, &w.divisor)
	return nil
}

// Conductor returns |delta|/gcd(|delta|,|b|), rejecting the neutral determinant separately.
func Conductor(delta, b, out *big.Int, w *Workspace) error {
	if delta.Sign() == 0 {
		return errors.New("neutral determinant has no conductor")
	}
	w.gcd.GCD(nil, nil, delta, b)
	w.next.Abs(delta)
	w.next.Quo(&w.next, &w.gcd)
	out.Set(&w.next)
	return nil
}

// IntegralFixedPoint supplies only an integral affine candidate; guards still require replay.
func IntegralFixedPoint(a *AffineData, out *big.Int, w *Workspace) (bool, error) {
	if a.Q.Sign() == 0 {
		return false, errors.New("affine presentation has a zero denominator")
	}
	w.delta.Sub(&a.Q, &a.P)
	if w.delta.Sign() == 0 {
		return false, errors.New("neutral determinant requires a separate offset check")
	}
	w.remainder.Rem(&a.B, &w.delta)
	if w.remainder.Sign() != 0 {
		return false, nil
	}
	out.Quo(&a.B, &w.delta)
	return true, nil
}

// RunChecks verifies four guarded cycles against their exact affine fixed points.
func RunChecks() error {
	controls := []struct {
		q, c, d string
		start   int64
		word    []Letter
	}{
		{"3", "1", "2", 1, []Letter{Affine, Divide, Divide}},
		{"2", "2", "-2", 1, []Letter{Affine, Divide, Divide}},
		{"-5", "31", "-6", 4, []Letter{Affine, Affine, Divide}},
		{"3", "5", "2", 5, []Letter{Affine, Divide, Divide}},
	}
	var w Workspace
	var endpoint, candidate big.Int
	var data AffineData
	for _, control := range controls {
		p, err := ParseParameters(control.q, control.c, control.d)
		if err != nil {
			return err
		}
		start := big.NewInt(control.start)
		if !ExecuteWord(&p, control.word, start, &endpoint, &w) || endpoint.Cmp(start) != 0 {
			return fmt.Errorf("guarded closure failed: %+v", control)
		}
		if err := RawWordAffine(&p, control.word, &data, &w); err != nil {
			return err
		}
		integral, err := IntegralFixedPoint(&data, &candidate, &w)
		if err != nil || !integral || candidate.Cmp(start) != 0 {
			return fmt.Errorf("affine closure failed: %+v: %v", control, err)
		}
	}
	fmt.Println("exact raw cycles verified: (3,1,2), (2,2,-2), (-5,31,-6), (3,5,2)")
	return nil
}

// main is the Makefile entry point for the bounded foundation controls.
func main() {
	if err := RunChecks(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
