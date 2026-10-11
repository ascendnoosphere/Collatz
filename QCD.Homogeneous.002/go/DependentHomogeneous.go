// SPDX-License-Identifier: CC-BY-4.0
// The dependent positive homogeneous classification with exact certificates.
package main

import (
	"errors"
	"fmt"
	"math/big"
)

// Parameters gives the primitive common-base presentation q=Base^U and D=Base^V.
type Parameters struct {
	Base uint64
	U    uint64
	V    uint64
}

// Map stores validated parameters and their exact coefficients.
type Map struct {
	Parameters Parameters
	base       big.Int
	q          big.Int
	d          big.Int
	period     uint64
}

// Workspace owns reusable integers used by decomposition, stepping, and verification.
type Workspace struct {
	quotient  big.Int
	remainder big.Int
	factor    big.Int
	current   big.Int
	next      big.Int
	power     big.Int
	exponent  big.Int
	height    big.Int
}

// Certificate records the canonical factor, transient, primitive cycle, and height bound.
type Certificate struct {
	Seed            big.Int
	BaseFree        big.Int
	TailStart       big.Int
	HeightBound     big.Int
	InitialExponent uint64
	TailExponent    uint64
	Transient       uint64
	Period          uint64
	Cycle           []big.Int
}

// Cache owns reusable certificate storage for allocation-free bounded loops.
type Cache struct {
	Built Certificate
}

// NewCache preallocates reusable cycle storage up to the stated primitive period.
func NewCache(maxPeriod uint64) (*Cache, error) {
	if maxPeriod > uint64(^uint(0)>>1) {
		return nil, errors.New("cache period does not fit an int")
	}
	cache := &Cache{}
	cache.Built.Cycle = make([]big.Int, 0, int(maxPeriod))
	return cache, nil
}

// GreatestCommonDivisor computes the Euclidean greatest common divisor.
func GreatestCommonDivisor(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// Validate checks the primitive common-base parameter contract.
func (p Parameters) Validate() error {
	if p.Base < 2 {
		return errors.New("base must be at least two")
	}
	if p.U == 0 || p.V == 0 {
		return errors.New("both exponents must be positive")
	}
	if p.U > ^uint64(0)-p.V {
		return errors.New("period overflows uint64")
	}
	if GreatestCommonDivisor(p.U, p.V) != 1 {
		return errors.New("exponents must be coprime")
	}
	return nil
}

// NewMap validates a primitive presentation and computes q and D exactly.
func NewMap(p Parameters) (*Map, error) {
	if err := p.Validate(); err != nil {
		return nil, err
	}
	m := &Map{Parameters: p, period: p.U + p.V}
	m.base.SetUint64(p.Base)
	var exponent big.Int
	exponent.SetUint64(p.U)
	m.q.Exp(&m.base, &exponent, nil)
	exponent.SetUint64(p.V)
	m.d.Exp(&m.base, &exponent, nil)
	return m, nil
}

// Coefficients copies q and D into caller-owned integers.
func (m *Map) Coefficients(q, d *big.Int) {
	q.Set(&m.q)
	d.Set(&m.d)
}

// Period returns the primitive raw period U+V.
func (m *Map) Period() uint64 {
	return m.period
}

// ExponentStep applies k-v when k>=v and k+u otherwise.
func (m *Map) ExponentStep(k uint64) uint64 {
	if k >= m.Parameters.V {
		return k - m.Parameters.V
	}
	return k + m.Parameters.U
}

// Step applies one positive homogeneous raw instruction.
func (m *Map) Step(dst, state *big.Int, w *Workspace) error {
	if state.Sign() <= 0 {
		return errors.New("state must be positive")
	}
	w.quotient.QuoRem(state, &m.d, &w.remainder)
	if w.remainder.Sign() == 0 {
		dst.Set(&w.quotient)
		return nil
	}
	dst.Mul(&m.q, state)
	return nil
}

// Decompose writes the base-free factor and returns the exact base exponent.
func (m *Map) Decompose(factor, state *big.Int, w *Workspace) (uint64, error) {
	if state.Sign() <= 0 {
		return 0, errors.New("state must be positive")
	}
	factor.Set(state)
	var exponent uint64
	for {
		w.quotient.QuoRem(factor, &m.base, &w.remainder)
		if w.remainder.Sign() != 0 {
			return exponent, nil
		}
		if exponent == ^uint64(0) {
			return 0, errors.New("base exponent overflows uint64")
		}
		factor.Set(&w.quotient)
		exponent++
	}
}

// BuildCertificateInto writes a certificate into caller-owned reusable storage.
func (m *Map) BuildCertificateInto(certificate *Certificate, seed *big.Int,
	w *Workspace) error {
	if certificate == nil {
		return errors.New("certificate is nil")
	}
	if seed.Sign() <= 0 {
		return errors.New("seed must be positive")
	}
	if m.period > uint64(^uint(0)>>1) {
		return errors.New("period does not fit an int")
	}
	period := int(m.period)
	if cap(certificate.Cycle) < period {
		return errors.New("certificate cycle capacity is too small")
	}
	certificate.Cycle = certificate.Cycle[:period]
	initialExponent, err := m.Decompose(&w.factor, seed, w)
	if err != nil {
		return err
	}
	certificate.Seed.Set(seed)
	certificate.BaseFree.Set(&w.factor)
	certificate.InitialExponent = initialExponent
	certificate.Period = m.period
	certificate.Transient = 0

	// Remove whole division blocks until the exponent lies in the recurrent interval.
	tailExponent := initialExponent
	for tailExponent >= m.period {
		tailExponent -= m.Parameters.V
		certificate.Transient++
	}
	certificate.TailExponent = tailExponent

	w.current.Set(seed)
	for step := uint64(0); step < certificate.Transient; step++ {
		if err := m.Step(&w.next, &w.current, w); err != nil {
			return err
		}
		w.current.Set(&w.next)
	}
	certificate.TailStart.Set(&w.current)

	// The proved source-relative bound is q*D*seed.
	w.height.Mul(&m.q, &m.d)
	w.height.Mul(&w.height, seed)
	certificate.HeightBound.Set(&w.height)
	if w.current.Cmp(&w.height) > 0 {
		return errors.New("tail start exceeds height bound")
	}

	for step := 0; step < period; step++ {
		for previous := 0; previous < step; previous++ {
			if certificate.Cycle[previous].Cmp(&w.current) == 0 {
				return errors.New("cycle returns before U+V steps")
			}
		}
		certificate.Cycle[step].Set(&w.current)
		if err := m.Step(&w.next, &w.current, w); err != nil {
			return err
		}
		if w.next.Cmp(&w.height) > 0 {
			return errors.New("cycle state exceeds height bound")
		}
		w.current.Set(&w.next)
	}
	if w.current.Cmp(&certificate.TailStart) != 0 {
		return errors.New("cycle does not return after U+V steps")
	}
	return nil
}

// BuildCertificate constructs an independently owned exact certificate.
func (m *Map) BuildCertificate(seed *big.Int, w *Workspace) (Certificate, error) {
	var certificate Certificate
	if m.period > uint64(^uint(0)>>1) {
		return certificate, errors.New("period does not fit an int")
	}
	certificate.Cycle = make([]big.Int, 0, int(m.period))
	err := m.BuildCertificateInto(&certificate, seed, w)
	return certificate, err
}

// VerifyCertificate recomputes and compares every field without mutating the certificate.
func (m *Map) VerifyCertificate(certificate *Certificate, w *Workspace) error {
	if certificate == nil {
		return errors.New("certificate is nil")
	}
	if certificate.Seed.Sign() <= 0 {
		return errors.New("certificate seed must be positive")
	}
	if m.period > uint64(^uint(0)>>1) {
		return errors.New("period does not fit an int")
	}
	period := int(m.period)
	if len(certificate.Cycle) != period {
		return errors.New("certificate cycle length mismatch")
	}
	initialExponent, err := m.Decompose(&w.factor, &certificate.Seed, w)
	if err != nil {
		return err
	}
	if certificate.BaseFree.Cmp(&w.factor) != 0 {
		return errors.New("certificate base-free factor mismatch")
	}

	tailExponent := initialExponent
	transient := uint64(0)
	for tailExponent >= m.period {
		tailExponent -= m.Parameters.V
		transient++
	}
	if certificate.InitialExponent != initialExponent ||
		certificate.TailExponent != tailExponent ||
		certificate.Transient != transient || certificate.Period != m.period {
		return errors.New("certificate scalar field mismatch")
	}

	w.current.Set(&certificate.Seed)
	for step := uint64(0); step < transient; step++ {
		if err := m.Step(&w.next, &w.current, w); err != nil {
			return err
		}
		w.current.Set(&w.next)
	}
	if certificate.TailStart.Cmp(&w.current) != 0 {
		return errors.New("certificate tail-start mismatch")
	}

	w.height.Mul(&m.q, &m.d)
	w.height.Mul(&w.height, &certificate.Seed)
	if certificate.HeightBound.Cmp(&w.height) != 0 {
		return errors.New("certificate height-bound mismatch")
	}
	for step := 0; step < period; step++ {
		for previous := 0; previous < step; previous++ {
			if certificate.Cycle[previous].Cmp(&w.current) == 0 {
				return errors.New("certificate cycle returns before U+V steps")
			}
		}
		if certificate.Cycle[step].Cmp(&w.current) != 0 {
			return fmt.Errorf("certificate cycle mismatch at index %d", step)
		}
		if w.current.Cmp(&w.height) > 0 {
			return errors.New("certificate cycle state exceeds height bound")
		}
		if err := m.Step(&w.next, &w.current, w); err != nil {
			return err
		}
		w.current.Set(&w.next)
	}
	if w.current.Cmp(&certificate.TailStart) != 0 {
		return errors.New("certificate cycle does not return after U+V steps")
	}
	return nil
}

// main verifies an exhaustive bounded family and one large exact relation.
func main() {
	var workspace Workspace
	var seed big.Int
	cache, err := NewCache(14)
	if err != nil {
		panic(err)
	}
	verified := uint64(0)
	for base := uint64(2); base <= 8; base++ {
		for u := uint64(1); u <= 7; u++ {
			for v := uint64(1); v <= 7; v++ {
				if GreatestCommonDivisor(u, v) != 1 {
					continue
				}
				m, err := NewMap(Parameters{Base: base, U: u, V: v})
				if err != nil {
					panic(err)
				}
				for n := uint64(1); n <= 250; n++ {
					seed.SetUint64(n)
					if buildErr := m.BuildCertificateInto(&cache.Built, &seed,
						&workspace); buildErr != nil {
						panic(buildErr)
					}
					if verifyErr := m.VerifyCertificate(&cache.Built,
						&workspace); verifyErr != nil {
						panic(verifyErr)
					}
					verified++
				}
			}
		}
	}

	largeMap, err := NewMap(Parameters{Base: 2, U: 19, V: 23})
	if err != nil {
		panic(err)
	}
	largeCache, err := NewCache(largeMap.Period())
	if err != nil {
		panic(err)
	}
	seed.Exp(big.NewInt(2), big.NewInt(300), nil)
	seed.Mul(&seed, big.NewInt(105))
	if err := largeMap.BuildCertificateInto(&largeCache.Built, &seed,
		&workspace); err != nil {
		panic(err)
	}
	if err := largeMap.VerifyCertificate(&largeCache.Built,
		&workspace); err != nil {
		panic(err)
	}
	fmt.Printf("verified %d bounded certificates and one %d-step large cycle\n",
		verified, largeCache.Built.Period)
}
