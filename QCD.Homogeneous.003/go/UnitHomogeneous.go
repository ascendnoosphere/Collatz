// SPDX-License-Identifier: CC-BY-4.0
// Exact certificates for the positive unit-multiplier homogeneous map.
package main

import (
	"errors"
	"fmt"
	"math/big"
)

// Map stores a validated divisor for the map n/D when D divides n and n otherwise.
type Map struct {
	d big.Int
}

// Workspace owns reusable integers used by decomposition, stepping, and verification.
type Workspace struct {
	quotient  big.Int
	remainder big.Int
	factor    big.Int
	current   big.Int
	next      big.Int
}

// Certificate records the canonical fixed point and its exact entry time.
type Certificate struct {
	Seed      big.Int
	Fixed     big.Int
	EntryTime uint64
}

// NewMap validates and copies an arbitrary-precision divisor.
func NewMap(d *big.Int) (*Map, error) {
	if d == nil || d.Cmp(big.NewInt(2)) < 0 {
		return nil, errors.New("divisor must be at least two")
	}
	m := &Map{}
	m.d.Set(d)
	return m, nil
}

// Validate rejects unset maps without allocating on the valid path.
func (m *Map) Validate() error {
	if m == nil || m.d.Sign() <= 0 || m.d.BitLen() < 2 {
		return errors.New("map divisor must be at least two")
	}
	return nil
}

// Divisor copies the map divisor into caller-owned storage.
func (m *Map) Divisor(d *big.Int) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if d == nil {
		return errors.New("destination is nil")
	}
	d.Set(&m.d)
	return nil
}

// Step applies one positive raw instruction and permits in-place use.
func (m *Map) Step(dst, state *big.Int, w *Workspace) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if dst == nil || w == nil {
		return errors.New("destination and workspace must be non-nil")
	}
	if state == nil || state.Sign() <= 0 {
		return errors.New("state must be positive")
	}
	w.quotient.QuoRem(state, &m.d, &w.remainder)
	if w.remainder.Sign() == 0 {
		dst.Set(&w.quotient)
		return nil
	}
	dst.Set(state)
	return nil
}

// Decompose writes the D-free factor and returns the exact D-adic exponent.
func (m *Map) Decompose(factor, state *big.Int, w *Workspace) (uint64, error) {
	if err := m.Validate(); err != nil {
		return 0, err
	}
	if factor == nil || w == nil {
		return 0, errors.New("factor and workspace must be non-nil")
	}
	if state == nil || state.Sign() <= 0 {
		return 0, errors.New("state must be positive")
	}
	factor.Set(state)
	var exponent uint64
	for {
		w.quotient.QuoRem(factor, &m.d, &w.remainder)
		if w.remainder.Sign() != 0 {
			return exponent, nil
		}
		if exponent == ^uint64(0) {
			return 0, errors.New("entry time overflows uint64")
		}
		factor.Set(&w.quotient)
		exponent++
	}
}

// BuildCertificateInto writes an exact certificate into reusable caller-owned storage.
func (m *Map) BuildCertificateInto(certificate *Certificate, seed *big.Int,
	w *Workspace) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if certificate == nil || w == nil {
		return errors.New("certificate and workspace must be non-nil")
	}
	entryTime, err := m.Decompose(&w.factor, seed, w)
	if err != nil {
		return err
	}
	certificate.Seed.Set(seed)
	certificate.Fixed.Set(&w.factor)
	certificate.EntryTime = entryTime
	return nil
}

// BuildCertificate constructs an independently owned exact certificate.
func (m *Map) BuildCertificate(seed *big.Int, w *Workspace) (Certificate, error) {
	var certificate Certificate
	err := m.BuildCertificateInto(&certificate, seed, w)
	return certificate, err
}

// VerifyCertificate checks the decomposition, exact first entry, and fixed tail.
func (m *Map) VerifyCertificate(certificate *Certificate, w *Workspace) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if certificate == nil || w == nil {
		return errors.New("certificate and workspace must be non-nil")
	}
	entryTime, err := m.Decompose(&w.factor, &certificate.Seed, w)
	if err != nil {
		return err
	}
	if certificate.Fixed.Cmp(&w.factor) != 0 {
		return errors.New("certificate fixed point mismatch")
	}
	if certificate.EntryTime != entryTime {
		return errors.New("certificate entry time mismatch")
	}

	// Replay every strict pre-entry state and the certified entry step.
	w.current.Set(&certificate.Seed)
	for step := uint64(0); step < entryTime; step++ {
		if w.current.Cmp(&certificate.Fixed) == 0 {
			return errors.New("orbit reaches the fixed point before the entry time")
		}
		if err := m.Step(&w.next, &w.current, w); err != nil {
			return err
		}
		w.current.Set(&w.next)
	}
	if w.current.Cmp(&certificate.Fixed) != 0 {
		return errors.New("orbit misses the fixed point at the entry time")
	}
	if err := m.Step(&w.next, &w.current, w); err != nil {
		return err
	}
	if w.next.Cmp(&certificate.Fixed) != 0 {
		return errors.New("certified state is not fixed")
	}
	return nil
}

// main verifies a bounded family and one large arbitrary-precision entry certificate.
func main() {
	var workspace Workspace
	var seed big.Int
	var certificate Certificate
	verified := uint64(0)

	// Exhaust every divisor and seed in the stated finite family.
	for divisor := uint64(2); divisor <= 96; divisor++ {
		m, err := NewMap(new(big.Int).SetUint64(divisor))
		if err != nil {
			panic(err)
		}
		for n := uint64(1); n <= 4096; n++ {
			seed.SetUint64(n)
			if err := m.BuildCertificateInto(&certificate, &seed, &workspace); err != nil {
				panic(err)
			}
			if err := m.VerifyCertificate(&certificate, &workspace); err != nil {
				panic(err)
			}
			verified++
		}
	}

	// Check an entry time far beyond the machine-word-sized state range.
	largeMap, err := NewMap(big.NewInt(37))
	if err != nil {
		panic(err)
	}
	seed.Exp(big.NewInt(37), big.NewInt(300), nil)
	seed.Mul(&seed, big.NewInt(53))
	if err := largeMap.BuildCertificateInto(&certificate, &seed, &workspace); err != nil {
		panic(err)
	}
	if err := largeMap.VerifyCertificate(&certificate, &workspace); err != nil {
		panic(err)
	}
	if certificate.EntryTime != 300 || certificate.Fixed.Cmp(big.NewInt(53)) != 0 {
		panic("large certificate has the wrong normal form")
	}
	fmt.Printf("verified %d bounded certificates and one %d-step large entry\n",
		verified, certificate.EntryTime)
}
