// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"errors"
	"fmt"
	"math/big"
	"sync"
)

// Outcome identifies the first finite-core or inaccessible endpoint.
type Outcome uint8

const (
	CoreOutcome Outcome = iota
	TrapOutcome
)

// Map owns immutable additive parameters and their exact access and core constants.
// Construct maps with NewMap; the zero value is invalid.
type Map struct {
	c, d, g, l, b, core, inverse, epsilon, decrement, one big.Int
}

// Workspace owns reusable arithmetic buffers and must not be shared between goroutines.
type Workspace struct {
	quotient, remainder, reduced, phase, affine, current, next big.Int
	rawTime, defect, power, nextPower                          big.Int
	blocks, budget                                             uint64
	outcome                                                    Outcome
}

// Certificate owns its integer fields independently of its input and workspace.
// Direct input-field aliases are supported; shallow copies of big.Int are not.
type Certificate struct {
	Seed, Reached, RawTime big.Int
	Blocks, Budget         uint64
	Outcome                Outcome
}

// NewMap computes the coprime access inverse and the exact integer core.
func NewMap(c, d *big.Int) (*Map, error) {
	if c == nil || c.Sign() <= 0 || d == nil || d.Sign() <= 0 || d.BitLen() < 2 {
		return nil, errors.New("require positive offset and divisor at least two")
	}
	m := new(Map)
	m.c.Set(c)
	m.d.Set(d)
	m.one.SetInt64(1)
	m.g.GCD(nil, nil, &m.c, &m.d)
	m.l.Quo(&m.d, &m.g)
	m.decrement.Sub(&m.d, &m.one)
	var reduced, index big.Int
	reduced.Quo(&m.c, &m.g)
	index.Sub(&m.l, &m.one)
	m.b.Mul(&m.c, &index)
	m.core.Quo(&m.b, &m.decrement)
	m.epsilon.Add(&m.core, &m.one)
	m.epsilon.Mul(&m.epsilon, &m.decrement)
	m.epsilon.Sub(&m.epsilon, &m.b)
	if m.l.Cmp(&m.one) > 0 && m.inverse.ModInverse(&reduced, &m.l) == nil {
		return nil, errors.New("normalized access multiplier is not invertible")
	}
	return m, nil
}

// Validate rejects uninitialized maps before any division or scratch-buffer access.
func (m *Map) Validate() error {
	if m == nil || m.c.Sign() <= 0 || m.d.Sign() <= 0 || m.d.BitLen() < 2 ||
		m.g.Sign() <= 0 || m.l.Sign() <= 0 || m.epsilon.Sign() <= 0 {
		return errors.New("map must be initialized with NewMap")
	}
	return nil
}

// Divisor returns an independently owned copy of the divisor.
func (m *Map) Divisor(dst *big.Int) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if dst == nil {
		return errors.New("nil divisor destination")
	}
	dst.Set(&m.d)
	return nil
}

// CoreRadius returns the exact finite-core radius without exposing map storage.
func (m *Map) CoreRadius(dst *big.Int) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if dst == nil {
		return errors.New("nil core destination")
	}
	dst.Set(&m.core)
	return nil
}

// Step executes one original raw instruction and permits dst == state.
func (m *Map) Step(dst, state *big.Int, w *Workspace) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if dst == nil || w == nil || state == nil || state.Sign() <= 0 {
		return errors.New("require destination, workspace, and positive state")
	}
	w.quotient.QuoRem(state, &m.d, &w.remainder)
	if w.remainder.Sign() == 0 {
		dst.Set(&w.quotient)
	} else {
		dst.Add(state, &m.c)
	}
	return nil
}

// GeometricBudget computes the least h with D^h epsilon greater than the shifted seed.
func (m *Map) GeometricBudget(seed *big.Int, w *Workspace) (uint64, error) {
	if err := m.Validate(); err != nil {
		return 0, err
	}
	if w == nil || seed == nil || seed.Sign() <= 0 {
		return 0, errors.New("require workspace and positive seed")
	}
	w.defect.Mul(&m.decrement, seed)
	w.defect.Sub(&w.defect, &m.b)
	w.power.Set(&m.epsilon)
	var h uint64
	// The positive power grows strictly; no floating-point logarithm is used.
	for w.power.Cmp(&w.defect) <= 0 {
		if h == ^uint64(0) {
			return 0, errors.New("geometric budget exceeds uint64")
		}
		w.nextPower.Mul(&w.power, &m.d)
		w.power.Set(&w.nextPower)
		h++
	}
	return h, nil
}

// Capture stores the first core-or-trap endpoint and reconstructs its entire raw clock.
// The scratch result is private; callers must copy it before reusing the workspace.
func (m *Map) Capture(seed *big.Int, w *Workspace) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if w == nil || seed == nil || seed.Sign() <= 0 {
		return errors.New("require workspace and positive seed")
	}
	budget, err := m.GeometricBudget(seed, w)
	if err != nil {
		return err
	}
	w.budget = budget
	w.current.Set(seed)
	w.rawTime.SetInt64(0)
	w.blocks = 0
	// Each accessible endpoint above the core strictly decreases the positive state.
	for {
		w.reduced.QuoRem(&w.current, &m.g, &w.remainder)
		if w.remainder.Sign() != 0 {
			w.outcome = TrapOutcome
			return nil
		}
		if w.current.Cmp(&m.core) <= 0 {
			w.outcome = CoreOutcome
			return nil
		}
		if w.blocks >= w.budget {
			return errors.New("geometric endpoint budget violated")
		}
		// Positive quotient/remainder realizes the negative residue with reusable buffers.
		w.phase.Mul(&w.reduced, &m.inverse)
		w.quotient.QuoRem(&w.phase, &m.l, &w.remainder)
		if w.remainder.Sign() == 0 {
			w.phase.SetInt64(0)
		} else {
			w.phase.Sub(&m.l, &w.remainder)
		}
		w.affine.Mul(&w.phase, &m.c)
		w.affine.Add(&w.affine, &w.current)
		w.next.QuoRem(&w.affine, &m.d, &w.remainder)
		if w.remainder.Sign() != 0 || w.next.Sign() <= 0 ||
			w.next.Cmp(&w.current) >= 0 {
			return errors.New("invalid first-division endpoint")
		}
		w.current.Set(&w.next)
		w.rawTime.Add(&w.rawTime, &w.phase)
		w.rawTime.Add(&w.rawTime, &m.one)
		w.blocks++
	}
}

// BuildCertificateInto copies only after the complete input orbit has been read.
func (m *Map) BuildCertificateInto(out *Certificate, seed *big.Int, w *Workspace) error {
	if out == nil {
		return errors.New("nil certificate destination")
	}
	if err := m.Capture(seed, w); err != nil {
		return err
	}
	out.Seed.Set(seed)
	out.Reached.Set(&w.current)
	out.RawTime.Set(&w.rawTime)
	out.Blocks = w.blocks
	out.Budget = w.budget
	out.Outcome = w.outcome
	return nil
}

// BuildCertificate constructs independent storage for a single seed.
func (m *Map) BuildCertificate(seed *big.Int, w *Workspace) (Certificate, error) {
	var out Certificate
	err := m.BuildCertificateInto(&out, seed, w)
	return out, err
}

// VerifyCertificate recomputes every field without writing into the supplied certificate.
func (m *Map) VerifyCertificate(certificate *Certificate, w *Workspace) error {
	if certificate == nil {
		return errors.New("nil certificate")
	}
	if err := m.Capture(&certificate.Seed, w); err != nil {
		return err
	}
	if certificate.Reached.Cmp(&w.current) != 0 ||
		certificate.RawTime.Cmp(&w.rawTime) != 0 || certificate.Blocks != w.blocks ||
		certificate.Budget != w.budget || certificate.Outcome != w.outcome {
		return errors.New("certificate does not match the exact first endpoint")
	}
	return nil
}

// CheckChunk scans a half-open divisor range with 2 <= first <= last <= 49.
// The nonnil output pointers must be owned exclusively by this worker.
func CheckChunk(first, last int, count *int, failure *error) {
	var w Workspace
	var c, d, seed big.Int
	var certificate Certificate
	for divisor := first; divisor < last; divisor++ {
		d.SetInt64(int64(divisor))
		for offset := int64(1); offset <= 32; offset++ {
			c.SetInt64(offset)
			m, err := NewMap(&c, &d)
			if err != nil {
				*failure = err
				return
			}
			// The warmed certificate and workspace are reused across this seed family.
			for n := int64(1); n <= 128; n++ {
				seed.SetInt64(n)
				if err := m.BuildCertificateInto(&certificate, &seed, &w); err != nil {
					*failure = err
					return
				}
				if err := m.VerifyCertificate(&certificate, &w); err != nil {
					*failure = err
					return
				}
				*count++
			}
		}
	}
}

// RunChecks executes bounded certificates and an exact large-seed entry.
func RunChecks() error {
	var wg sync.WaitGroup
	var counts [4]int
	var failures [4]error
	// Divisor ranges are disjoint; each worker owns its workspace and result slots.
	for worker := 0; worker < len(counts); worker++ {
		first := 2 + worker*12
		last := first + 12
		if last > 49 {
			last = 49
		}
		wg.Add(1)
		go func(slot, first, last int) {
			defer wg.Done()
			CheckChunk(first, last, &counts[slot], &failures[slot])
		}(worker, first, last)
	}
	wg.Wait()
	count := 0
	for worker, failure := range failures {
		if failure != nil {
			return failure
		}
		count += counts[worker]
	}
	m, err := NewMap(big.NewInt(1), big.NewInt(37))
	if err != nil {
		return err
	}
	var w Workspace
	seed := new(big.Int).Exp(big.NewInt(37), big.NewInt(300), nil)
	seed.Mul(seed, big.NewInt(53))
	certificate, err := m.BuildCertificate(seed, &w)
	if err != nil {
		return err
	}
	if err := m.VerifyCertificate(&certificate, &w); err != nil {
		return err
	}
	if certificate.Outcome != CoreOutcome || certificate.Reached.Cmp(big.NewInt(1)) != 0 ||
		certificate.Blocks != 302 || certificate.RawTime.Cmp(big.NewInt(358)) != 0 {
		return errors.New("large-seed endpoint or raw clock mismatch")
	}
	fmt.Printf("verified %d bounded certificates and one 302-block large entry\n", count)
	return nil
}

// main exits unsuccessfully if any exact certificate fails.
func main() {
	if err := RunChecks(); err != nil {
		panic(err)
	}
}
