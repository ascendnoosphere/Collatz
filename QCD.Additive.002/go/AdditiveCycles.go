// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"errors"
	"fmt"
	"math/big"
	"sync"
)

// ErrEnumerationBudget distinguishes an unfinished search from a complete empty answer.
var ErrEnumerationBudget = errors.New("cofactor exceeds the enumeration budget")

// Map owns immutable parameters and the canonical offset decomposition.
// Construct maps with NewMap; do not shallow-copy their big.Int fields.
type Map struct {
	c, d, s, t, g, l, window, inverse, accessInverse, decrement, one big.Int
	ready                                                            bool
}

// Workspace owns reusable arithmetic and snapshot buffers, one instance per goroutine.
type Workspace struct {
	product, numerator, quotient, remainder, sum, additions, phase, state big.Int
	reduced, access, accessRemainder, gcd, modulus, h, clock, grouped     big.Int
	power, unit                                                           big.Int
	snapshot                                                              []big.Int
}

// Certificate owns a primitive orbit's positive representatives and exact clocks.
// The first representative is the minimum; the closing vertex is not repeated.
type Certificate struct {
	Representatives                  []big.Int
	HPeriod, RawPeriod, OrderModulus big.Int
}

// Cache owns a reusable enumeration table and its borrowed callback certificate.
type Cache struct {
	visited     []bool
	phases      []big.Int
	certificate Certificate
}

// Enumeration records whether all cycles were exhausted, not merely whether some were found.
// EmptyWindow permits a complete zero-cycle answer without scanning the permutation.
type Enumeration struct {
	Cofactor              big.Int
	Visited, Cycles       uint64
	Complete, EmptyWindow bool
}

// NewMap removes divisor-supported factors by strictly decreasing gcd division.
func NewMap(c, d *big.Int) (*Map, error) {
	if c == nil || c.Sign() <= 0 || d == nil || d.Sign() <= 0 || d.BitLen() < 2 {
		return nil, errors.New("require positive offset and divisor at least two")
	}
	m := new(Map)
	m.c.Set(c)
	m.d.Set(d)
	m.one.SetInt64(1)
	m.s.SetInt64(1)
	m.t.Set(c)
	var factor, reduced, index big.Int
	// Each nonunit gcd removes a factor at least two from the remaining cofactor.
	for {
		factor.GCD(nil, nil, &m.t, &m.d)
		if factor.Cmp(&m.one) == 0 {
			break
		}
		m.t.Quo(&m.t, &factor)
		m.s.Mul(&m.s, &factor)
	}
	m.g.GCD(nil, nil, &m.c, &m.d)
	m.l.Quo(&m.d, &m.g)
	m.decrement.Sub(&m.d, &m.one)
	index.Sub(&m.l, &m.one)
	m.window.Mul(&m.t, &index)
	m.window.Quo(&m.window, &m.decrement)
	if m.t.Cmp(&m.one) > 0 && m.inverse.ModInverse(&m.d, &m.t) == nil {
		return nil, errors.New("divisor is not invertible modulo the cofactor")
	}
	reduced.Quo(&m.c, &m.g)
	if m.l.Cmp(&m.one) > 0 && m.accessInverse.ModInverse(&reduced, &m.l) == nil {
		return nil, errors.New("normalized access multiplier is not invertible")
	}
	m.ready = true
	return m, nil
}

// Validate rejects nil and uninitialized maps before buffer or divisor access.
func (m *Map) Validate() error {
	if m == nil || !m.ready {
		return errors.New("map must be initialized with NewMap")
	}
	return nil
}

// Decomposition returns independent copies without exposing mutable parameter storage.
func (m *Map) Decomposition(s, t, window *big.Int) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if s == nil || t == nil || window == nil || s == t || s == window || t == window {
		return errors.New("require three distinct decomposition destinations")
	}
	s.Set(&m.s)
	t.Set(&m.t)
	window.Set(&m.window)
	return nil
}

// RawState scales a positive window representative, without asserting cycle membership.
// The destination may be the representative itself.
func (m *Map) RawState(dst, representative *big.Int) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if dst == nil || representative == nil || representative.Sign() <= 0 ||
		representative.Cmp(&m.window) > 0 {
		return errors.New("require destination and a positive window representative")
	}
	dst.Mul(&m.s, representative)
	return nil
}

// Snapshot preserves all inputs before any possible output-field alias is changed.
func (w *Workspace) Snapshot(representatives []big.Int) {
	if cap(w.snapshot) < len(representatives) {
		w.snapshot = make([]big.Int, len(representatives))
	} else {
		w.snapshot = w.snapshot[:len(representatives)]
	}
	for i := range representatives {
		w.snapshot[i].Set(&representatives[i])
	}
}

// Compute checks a complete primitive modular orbit and derives its exact raw clock.
// Integer access uniqueness checks every early guard without iterating a huge raw period.
func (m *Map) Compute(representatives []big.Int, w *Workspace) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if w == nil {
		return errors.New("require arithmetic workspace")
	}
	if len(representatives) == 0 {
		return errors.New("a positive cycle must contain a representative")
	}
	representatives = representatives[:len(representatives)]
	first := &representatives[0]
	// Positive representatives include t for residue zero, never the integer zero.
	for i := range representatives {
		value := &representatives[i]
		if value.Sign() <= 0 || value.Cmp(&m.window) > 0 {
			return errors.New("representative lies outside the positive cycle window")
		}
		if value.Cmp(first) < 0 {
			return errors.New("first representative is not the cycle minimum")
		}
		if i > 0 && value.Cmp(first) == 0 {
			return errors.New("cycle repeats its first representative before closure")
		}
	}
	w.sum.SetInt64(0)
	w.additions.SetInt64(0)
	// A unit permutation and no early root return imply all representatives are distinct.
	for i := range representatives {
		next := i + 1
		if next == len(representatives) {
			next = 0
		}
		w.product.Mul(&m.d, &representatives[next])
		w.numerator.Sub(&w.product, &representatives[i])
		if w.numerator.Sign() < 0 {
			return errors.New("negative modular edge numerator")
		}
		w.quotient.QuoRem(&w.numerator, &m.t, &w.remainder)
		if w.remainder.Sign() != 0 || w.quotient.Cmp(&m.l) >= 0 {
			return errors.New("edge is not a legal first-division index")
		}
		w.state.Mul(&m.s, &representatives[i])
		w.reduced.QuoRem(&w.state, &m.g, &w.remainder)
		if w.remainder.Sign() != 0 {
			return errors.New("lifted edge is inaccessible")
		}
		w.access.Mul(&w.reduced, &m.accessInverse)
		w.access.QuoRem(&w.access, &m.l, &w.accessRemainder)
		if w.accessRemainder.Sign() == 0 {
			w.phase.SetInt64(0)
		} else {
			w.phase.Sub(&m.l, &w.accessRemainder)
		}
		if w.phase.Cmp(&w.quotient) != 0 {
			return errors.New("edge index differs from the unique first access")
		}
		w.sum.Add(&w.sum, &representatives[i])
		w.additions.Add(&w.additions, &w.quotient)
	}
	w.h.SetUint64(uint64(len(representatives)))
	w.clock.Add(&w.additions, &w.h)
	w.product.Mul(&m.decrement, &w.sum)
	w.grouped.QuoRem(&w.product, &m.t, &w.remainder)
	if w.remainder.Sign() != 0 {
		return errors.New("grouped raw clock is not integral")
	}
	w.grouped.Add(&w.grouped, &w.h)
	if w.grouped.Cmp(&w.clock) != 0 {
		return errors.New("edge clock and grouped clock differ")
	}
	// The effective modulus removes the representative's common factor, not the offset s.
	w.gcd.GCD(nil, nil, first, &m.t)
	w.modulus.Quo(&m.t, &w.gcd)
	w.power.Exp(&m.d, &w.h, &w.modulus)
	w.unit.Mod(&m.one, &w.modulus)
	if w.power.Cmp(&w.unit) != 0 {
		return errors.New("period does not close at the effective modulus")
	}
	return nil
}

// BuildCycle creates an owned certificate, supporting representatives == dst.Representatives.
// Failed checks leave dst unchanged; shallow copies of big.Int storage are not supported.
func (m *Map) BuildCycle(dst *Certificate, representatives []big.Int, w *Workspace) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if dst == nil || w == nil {
		return errors.New("require certificate destination and workspace")
	}
	w.Snapshot(representatives)
	if err := m.Compute(w.snapshot, w); err != nil {
		return err
	}
	if cap(dst.Representatives) < len(w.snapshot) {
		dst.Representatives = make([]big.Int, len(w.snapshot))
	} else {
		dst.Representatives = dst.Representatives[:len(w.snapshot)]
	}
	for i := range w.snapshot {
		dst.Representatives[i].Set(&w.snapshot[i])
	}
	dst.HPeriod.Set(&w.h)
	dst.RawPeriod.Set(&w.clock)
	dst.OrderModulus.Set(&w.modulus)
	return nil
}

// Verify recomputes every claimed field without modifying the supplied certificate.
func (m *Map) Verify(certificate *Certificate, w *Workspace) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if certificate == nil || w == nil {
		return errors.New("require certificate and workspace")
	}
	if err := m.Compute(certificate.Representatives, w); err != nil {
		return err
	}
	if certificate.HPeriod.Cmp(&w.h) != 0 || certificate.RawPeriod.Cmp(&w.clock) != 0 ||
		certificate.OrderModulus.Cmp(&w.modulus) != 0 {
		return errors.New("certificate period or effective modulus differs")
	}
	return nil
}

// CopyFrom deep-copies a certificate for retention beyond an enumeration callback.
func (dst *Certificate) CopyFrom(src *Certificate) error {
	if dst == nil || src == nil {
		return errors.New("require certificate source and destination")
	}
	if dst == src {
		return nil
	}
	dst.Representatives = make([]big.Int, len(src.Representatives))
	for i := range src.Representatives {
		dst.Representatives[i].Set(&src.Representatives[i])
	}
	dst.HPeriod.Set(&src.HPeriod)
	dst.RawPeriod.Set(&src.RawPeriod)
	dst.OrderModulus.Set(&src.OrderModulus)
	return nil
}

// Prepare reserves enumeration storage before the permutation's inner edge loops.
func (cache *Cache) Prepare(n int, w *Workspace) {
	if cap(cache.visited) < n+1 {
		cache.visited = make([]bool, n+1)
	} else {
		cache.visited = cache.visited[:n+1]
		clear(cache.visited)
	}
	if cap(cache.phases) < n {
		cache.phases = make([]big.Int, n)
	} else {
		cache.phases = cache.phases[:n]
	}
	if cap(cache.certificate.Representatives) < n {
		cache.certificate.Representatives = make([]big.Int, n)
	} else {
		cache.certificate.Representatives = cache.certificate.Representatives[:n]
	}
	// One machine-word representative fits every phase, output, and snapshot buffer.
	for i := range cache.phases {
		cache.phases[i].SetUint64(uint64(n))
		cache.certificate.Representatives[i].SetUint64(uint64(n))
	}
	w.Snapshot(cache.phases)
}

// Enumerate visits each complete surviving orbit once, with a read-only borrowed certificate.
// Deep-copy retained data; do not reenter with the same cache during a callback.
// Cache and workspace are goroutine-local; callbacks may verify with the supplied workspace.
// Parameters and clocks stay arbitrary precision; only enumeration capacity is machine-sized.
func (m *Map) Enumerate(limit int, cache *Cache, w *Workspace,
	visit func(*Certificate) error) (Enumeration, error) {
	var report Enumeration
	if err := m.Validate(); err != nil {
		return report, err
	}
	report.Cofactor.Set(&m.t)
	if limit < 0 || cache == nil || w == nil || visit == nil {
		return report, errors.New("require nonnegative budget, cache, workspace, and callback")
	}
	if m.window.Sign() == 0 {
		report.Complete = true
		report.EmptyWindow = true
		return report, nil
	}
	maxInt := uint64(^uint(0) >> 1)
	if !m.t.IsUint64() || m.t.Uint64() > uint64(limit) || m.t.Uint64() >= maxInt {
		return report, ErrEnumerationBudget
	}
	n := int(m.t.Uint64())
	cache.Prepare(n, w)
	visited := cache.visited[:n+1]
	phases := cache.phases[:n]
	// Entire permutation orbits are consumed even after one vertex fails the window.
	for seed := 1; seed <= n; seed++ {
		if visited[seed] {
			continue
		}
		state, h, survives := seed, 0, true
		for !visited[state] {
			visited[state] = true
			report.Visited++
			phases[h].SetUint64(uint64(state))
			if phases[h].Cmp(&m.window) > 0 {
				survives = false
			}
			w.phase.SetUint64(uint64(state))
			w.product.Mul(&m.inverse, &w.phase)
			w.phase.Mod(&w.product, &m.t)
			if w.phase.Sign() == 0 {
				w.phase.Set(&m.t)
			}
			state = int(w.phase.Uint64())
			h++
		}
		if state != seed {
			return report, errors.New("inverse permutation unexpectedly merged two orbits")
		}
		if !survives {
			continue
		}
		if err := m.BuildCycle(&cache.certificate, phases[:h], w); err != nil {
			return report, err
		}
		if err := visit(&cache.certificate); err != nil {
			return report, err
		}
		report.Cycles++
	}
	report.Complete = true
	return report, nil
}

// CheckChunk checks independent parameter cells with privately owned arithmetic buffers.
// The interval is half-open; count and failure must be nonnil, exclusively owned slots.
func CheckChunk(first, last int, count *uint64, failure *error) {
	var cache Cache
	var w Workspace
	var c, d big.Int
	for divisor := first; divisor < last; divisor++ {
		d.SetInt64(int64(divisor))
		for offset := 1; offset <= 96; offset++ {
			c.SetInt64(int64(offset))
			m, err := NewMap(&c, &d)
			if err != nil {
				*failure = err
				return
			}
			report, err := m.Enumerate(96, &cache, &w, func(cert *Certificate) error {
				return m.Verify(cert, &w)
			})
			if err != nil || !report.Complete {
				*failure = fmt.Errorf("c=%d D=%d: enumeration: %v", offset, divisor, err)
				return
			}
			*count += report.Cycles
		}
	}
}

// main checks four disjoint parameter chunks and an algebraically certified huge raw clock.
func main() {
	var counts [4]uint64
	var failures [4]error
	var group sync.WaitGroup
	bounds := [5]int{2, 14, 26, 38, 49}
	for i := range counts {
		group.Add(1)
		go func(i int) {
			defer group.Done()
			CheckChunk(bounds[i], bounds[i+1], &counts[i], &failures[i])
		}(i)
	}
	group.Wait()
	var total uint64
	for i := range counts {
		if failures[i] != nil {
			panic(failures[i])
		}
		total += counts[i]
	}
	var one, divisor big.Int
	one.SetInt64(1)
	divisor.Lsh(&one, 200)
	m, err := NewMap(&one, &divisor)
	if err != nil {
		panic(err)
	}
	var w Workspace
	var cert Certificate
	var representatives [1]big.Int
	representatives[0].Set(&one)
	if err := m.BuildCycle(&cert, representatives[:], &w); err != nil {
		panic(err)
	}
	if err := m.Verify(&cert, &w); err != nil || cert.RawPeriod.Cmp(&divisor) != 0 {
		panic("large raw-period certificate failed")
	}
	fmt.Printf("verified %d primitive cycles across 4512 parameter pairs; "+
		"certified raw period 2^200 without raw replay\n", total)
}
