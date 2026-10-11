// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"errors"
	"fmt"
	"math/big"
	"math/bits"
	"sync"
)

// Outcome distinguishes a positive raw return from an inaccessible affine tail.
type Outcome uint8

const (
	Trap Outcome = iota + 1
	Periodic
)

// ErrResource means that no outcome certificate was produced within the requested limits.
var ErrResource = errors.New("outcome resource limit exceeded")

// Limits bounds recorded events and dense core entries, including the unused entry zero.
type Limits struct {
	MaxBlocks   uint64
	CoreEntries int
}

// Map owns immutable positive additive parameters and their normalized access constants.
// The zero value is invalid; construct maps with NewMap.
type Map struct {
	c, d, g, l, inverse, core, one big.Int
}

// Certificate records exact raw clocks, not a least-period claim.
// Integer fields own their storage; shallow copies of big.Int are unsupported.
type Certificate struct {
	Seed, Phase, Clock, Period big.Int
	Blocks, PrefixBlocks       uint64
	Outcome                    Outcome
}

// Workspace owns arithmetic and prefix buffers; each concurrent caller needs its own instance.
type Workspace struct {
	seed, state, next, quotient, remainder, index, numerator big.Int
	clock, weight, savedPhase, savedClock, difference        big.Int
}

// Cache owns finite-core history; its clock buffers have disjoint backing storage.
type Cache struct {
	seen   []bool
	blocks []uint64
	clocks []big.Int
	words  []big.Word
}

// NewMap computes the exact core and the unit inverse after removing the common gcd.
func NewMap(c, d *big.Int) (*Map, error) {
	if c == nil || c.Sign() <= 0 || d == nil || d.Cmp(big.NewInt(2)) < 0 {
		return nil, errors.New("require positive offset and divisor at least two")
	}
	m := new(Map)
	m.c.Set(c)
	m.d.Set(d)
	m.one.SetInt64(1)
	m.g.GCD(nil, nil, &m.c, &m.d)
	m.l.Quo(&m.d, &m.g)
	var reduced, displacement, decrement big.Int
	reduced.Quo(&m.c, &m.g)
	if m.l.Cmp(&m.one) > 0 && m.inverse.ModInverse(&reduced, &m.l) == nil {
		return nil, errors.New("normalized access multiplier is not invertible")
	}
	displacement.Sub(&m.l, &m.one)
	displacement.Mul(&displacement, &m.c)
	decrement.Sub(&m.d, &m.one)
	m.core.Quo(&displacement, &decrement)
	return m, nil
}

// Validate prevents division or scratch access through an uninitialized map.
func (m *Map) Validate() error {
	if m == nil || m.c.Sign() <= 0 || m.d.BitLen() < 2 || m.d.Sign() <= 0 ||
		m.g.Sign() <= 0 || m.l.Sign() <= 0 {
		return errors.New("map must be initialized with NewMap")
	}
	return nil
}

// AllSeedsPeriodic decides the universal positive-seed statement by the proved gcd criterion.
func (m *Map) AllSeedsPeriodic() (bool, error) {
	if err := m.Validate(); err != nil {
		return false, err
	}
	return m.g.Cmp(&m.one) == 0, nil
}

// CoreRadius copies the core bound without exposing immutable map storage.
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

// Warm reserves a known arithmetic width without allocating during subsequent small operations.
// This setup helper accepts an initialized, nonnil integer.
func Warm(z *big.Int, words int) {
	if cap(z.Bits()) < words {
		z.SetBits(make([]big.Word, words))
		z.SetInt64(0)
	}
}

// Prepare snapshots the input before warming mutable fields, including direct input aliases.
func (w *Workspace) Prepare(m *Map, seed *big.Int) error {
	if err := m.Validate(); err != nil {
		return err
	}
	if w == nil || seed == nil || seed.Sign() <= 0 {
		return errors.New("require workspace and positive seed")
	}
	w.seed.Set(seed)
	maxInt := int(^uint(0) >> 1)
	if w.seed.BitLen() > maxInt-m.c.BitLen()-m.d.BitLen()-128 {
		return ErrResource
	}
	width := w.seed.BitLen() + m.c.BitLen() + m.d.BitLen() + 128
	words := (width + bits.UintSize - 1) / bits.UintSize
	fields := []*big.Int{&w.state, &w.next, &w.quotient, &w.remainder, &w.index,
		&w.numerator, &w.clock, &w.weight, &w.savedPhase, &w.savedClock, &w.difference}
	for _, field := range fields {
		Warm(field, words)
	}
	w.state.Set(&w.seed)
	w.clock.SetInt64(0)
	return nil
}

// Prepare resets dense history, rejecting unrepresentable or overflowing capacities.
func (cache *Cache) Prepare(entries, words int) error {
	maxInt := int(^uint(0) >> 1)
	if cache == nil || entries <= 0 || words <= 0 || entries > maxInt/words {
		return ErrResource
	}
	if cap(cache.seen) < entries {
		cache.seen = make([]bool, entries)
		cache.blocks = make([]uint64, entries)
		cache.clocks = make([]big.Int, entries)
	} else {
		cache.seen = cache.seen[:entries]
		cache.blocks = cache.blocks[:entries]
		cache.clocks = cache.clocks[:entries]
	}
	storage := entries * words
	if cap(cache.words) < storage {
		cache.words = make([]big.Word, storage)
	} else {
		cache.words = cache.words[:storage]
	}
	clear(cache.seen)
	// Every clock gets an exclusive full-capacity slice; reset old values before reuse.
	for i := 0; i < entries; i++ {
		start, end := i*words, (i+1)*words
		cache.clocks[i].SetBits(cache.words[start:end:end])
		cache.clocks[i].SetInt64(0)
	}
	return nil
}

// Accessible tests the true division-access criterion at the current phase.
func (m *Map) Accessible(w *Workspace) bool {
	w.quotient.QuoRem(&w.state, &m.g, &w.remainder)
	return w.remainder.Sign() == 0
}

// Event executes exactly one first division and its full raw clock.
// Call with a valid map and prepared, positive workspace state.
func (m *Map) Event(w *Workspace) error {
	if !m.Accessible(w) {
		return errors.New("cannot advance an inaccessible phase")
	}
	w.index.Mul(&w.quotient, &m.inverse)
	w.index.Neg(&w.index)
	w.index.Mod(&w.index, &m.l)
	w.numerator.Mul(&w.index, &m.c)
	w.numerator.Add(&w.numerator, &w.state)
	w.next.QuoRem(&w.numerator, &m.d, &w.remainder)
	if w.remainder.Sign() != 0 || w.next.Sign() <= 0 {
		return errors.New("first division failed its exact endpoint certificate")
	}
	if w.state.Cmp(&m.core) > 0 && w.next.Cmp(&w.state) >= 0 {
		return errors.New("above-core event failed strict descent")
	}
	if w.state.Cmp(&m.core) <= 0 && w.next.Cmp(&m.core) > 0 {
		return errors.New("event left the invariant finite core")
	}
	w.weight.Add(&w.index, &m.one)
	w.clock.Add(&w.clock, &w.weight)
	w.state.Set(&w.next)
	return nil
}

// Store copies a completed witness, never borrowing mutable cache or workspace integers.
// Its arguments are initialized internal buffers.
func Store(out *Certificate, w *Workspace, kind Outcome, blocks, prefix uint64) {
	out.Seed.Set(&w.seed)
	out.Phase.Set(&w.savedPhase)
	out.Clock.Set(&w.savedClock)
	out.Period.Set(&w.difference)
	out.Blocks, out.PrefixBlocks, out.Outcome = blocks, prefix, kind
}

// Classify stops at a true trap or the first repeated core event phase.
// Refusal leaves out unchanged; dense memory is requested only after accessible core entry.
func (m *Map) Classify(seed *big.Int, limits Limits, cache *Cache,
	w *Workspace, out *Certificate) error {
	if cache == nil || out == nil || limits.CoreEntries < 0 {
		return errors.New("require cache, output, and nonnegative core capacity")
	}
	if err := w.Prepare(m, seed); err != nil {
		return err
	}
	prepared := false
	var blocks uint64
	for {
		if !m.Accessible(w) {
			w.savedPhase.Set(&w.state)
			w.savedClock.Set(&w.clock)
			w.difference.SetInt64(0)
			Store(out, w, Trap, blocks, blocks)
			return nil
		}
		if w.state.Cmp(&m.core) <= 0 {
			if !prepared {
				maxInt := int(^uint(0) >> 1)
				if !m.core.IsInt64() || m.core.Int64() >= int64(maxInt) {
					return ErrResource
				}
				entries := int(m.core.Int64()) + 1
				if entries > limits.CoreEntries {
					return ErrResource
				}
				if err := cache.Prepare(entries, cap(w.clock.Bits())); err != nil {
					return err
				}
				prepared = true
			}
			slot := int(w.state.Int64())
			if cache.seen[slot] {
				w.savedPhase.Set(&w.state)
				w.savedClock.Set(&cache.clocks[slot])
				w.difference.Sub(&w.clock, &w.savedClock)
				if w.difference.Sign() <= 0 {
					return errors.New("repeated accessible phase has nonpositive raw period")
				}
				Store(out, w, Periodic, blocks, cache.blocks[slot])
				return nil
			}
			cache.seen[slot] = true
			cache.blocks[slot] = blocks
			cache.clocks[slot].Set(&w.clock)
		}
		if blocks == limits.MaxBlocks {
			return ErrResource
		}
		if err := m.Event(w); err != nil {
			return err
		}
		blocks++
	}
}

// Verify checks a supplied finite event trace independently of dense history or search.
// A periodic certificate asserts a positive return, not necessarily the least period.
func (m *Map) Verify(cert *Certificate, maxBlocks uint64, w *Workspace) error {
	if cert == nil || cert.Seed.Sign() <= 0 || cert.Phase.Sign() <= 0 ||
		cert.Clock.Sign() < 0 || cert.Period.Sign() < 0 || cert.PrefixBlocks > cert.Blocks {
		return errors.New("invalid outcome certificate header")
	}
	if cert.Outcome != Trap && cert.Outcome != Periodic {
		return errors.New("unknown outcome certificate tag")
	}
	if cert.Outcome == Trap && (cert.Period.Sign() != 0 || cert.PrefixBlocks != cert.Blocks) {
		return errors.New("trap certificate contains a return interval")
	}
	if cert.Outcome == Periodic &&
		(cert.Period.Sign() <= 0 || cert.PrefixBlocks == cert.Blocks) {
		return errors.New("periodic certificate needs a positive event interval")
	}
	if cert.Blocks > maxBlocks {
		return ErrResource
	}
	if err := w.Prepare(m, &cert.Seed); err != nil {
		return err
	}
	// The explicit endpoint check precedes increment, so even a uint64 maximal bound cannot wrap.
	for i := uint64(0); ; i++ {
		if i == cert.PrefixBlocks {
			w.savedPhase.Set(&w.state)
			w.savedClock.Set(&w.clock)
		}
		if i == cert.Blocks {
			break
		}
		if err := m.Event(w); err != nil {
			return err
		}
	}
	if w.savedPhase.Cmp(&cert.Phase) != 0 || w.savedClock.Cmp(&cert.Clock) != 0 {
		return errors.New("outcome prefix does not match its raw clock and phase")
	}
	if cert.Outcome == Trap {
		if m.Accessible(w) {
			return errors.New("claimed trap is accessible")
		}
	} else {
		w.difference.Sub(&w.clock, &w.savedClock)
		if w.state.Cmp(&cert.Phase) != 0 || w.difference.Cmp(&cert.Period) != 0 {
			return errors.New("claimed return does not close at the specified raw period")
		}
	}
	return nil
}

// CheckChunk compares bounded certificates with the original instruction map.
// Each goroutine owns its cache, arithmetic, certificate, and nonnil count/failure slots.
func CheckChunk(first, last int, count *int, failure *error) {
	var cache Cache
	var w, verifier Workspace
	var cert Certificate
	var seed, cValue, dValue big.Int
	for d := first; d < last; d++ {
		dValue.SetInt64(int64(d))
		for c := 1; c <= 32; c++ {
			cValue.SetInt64(int64(c))
			m, err := NewMap(&cValue, &dValue)
			if err != nil {
				*failure = err
				return
			}
			for n := 1; n <= 128; n++ {
				seed.SetInt64(int64(n))
				if err = m.Classify(&seed, Limits{1024, 33},
					&cache, &w, &cert); err != nil {
					*failure = err
					return
				}
				if err = m.Verify(&cert, 1024, &verifier); err != nil {
					*failure = err
					return
				}
				state := n
				clock := int(cert.Clock.Int64())
				period := int(cert.Period.Int64())
				for i := 0; i < clock+period; i++ {
					if i == clock && int(cert.Phase.Int64()) != state {
						*failure = errors.New("raw prefix comparison failed")
						return
					}
					if state%d == 0 {
						state /= d
					} else {
						state += c
					}
				}
				if state != int(cert.Phase.Int64()) ||
					(cert.Outcome == Trap && state%int(m.g.Int64()) == 0) {
					*failure = errors.New("raw outcome comparison failed")
					return
				}
				*count++
			}
		}
	}
}

// main verifies four independent half-open divisor chunks and one huge raw-clock certificate.
func main() {
	var wg sync.WaitGroup
	var counts [4]int
	var failures [4]error
	bounds := [5]int{2, 8, 14, 20, 25}
	for i := 0; i < len(counts); i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			CheckChunk(bounds[i], bounds[i+1], &counts[i], &failures[i])
		}(i)
	}
	wg.Wait()
	total := 0
	for i, err := range failures {
		if err != nil {
			panic(err)
		}
		total += counts[i]
	}
	d := new(big.Int).Lsh(big.NewInt(1), 200)
	m, err := NewMap(big.NewInt(1), d)
	if err != nil {
		panic(err)
	}
	var cache Cache
	var w, verifier Workspace
	var cert Certificate
	if err = m.Classify(big.NewInt(1), Limits{1, 2}, &cache, &w, &cert); err != nil {
		panic(err)
	}
	if err = m.Verify(&cert, 1, &verifier); err != nil || cert.Period.Cmp(d) != 0 {
		panic("huge raw-clock certificate failed")
	}
	fmt.Printf("verified %d bounded outcomes and one 201-bit raw period\n", total)
}
