// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"errors"
	"math/big"
	"math/bits"
	"testing"
)

// CopyCertificate gives fault-injection tests independent integer ownership.
func CopyCertificate(dst, src *Certificate) {
	dst.Seed.Set(&src.Seed)
	dst.Phase.Set(&src.Phase)
	dst.Clock.Set(&src.Clock)
	dst.Period.Set(&src.Period)
	dst.Blocks, dst.PrefixBlocks, dst.Outcome = src.Blocks, src.PrefixBlocks, src.Outcome
}

// ReferenceGcd computes the trap criterion without the production constructor.
func ReferenceGcd(c, d int) int {
	for d != 0 {
		c, d = d, c%d
	}
	return c
}

// ReferenceOutcome follows original raw instructions and their first repeated state.
// The bounded test parameters make the stated finite cap and every integer operation safe.
func ReferenceOutcome(c, d, seed int) (Outcome, int, error) {
	seen := make(map[int]int, c*d+seed+1)
	g := ReferenceGcd(c, d)
	state := seed
	for clock := 0; clock <= (seed+2*c)*d+2; clock++ {
		if state%g != 0 {
			return Trap, 0, nil
		}
		if previous, found := seen[state]; found {
			return Periodic, clock - previous, nil
		}
		seen[state] = clock
		if state%d == 0 {
			state /= d
		} else {
			state += c
		}
	}
	return 0, 0, errors.New("raw reference exhausted its proved bounded cap")
}

// TestRawReference compares outcome tags and least raw periods against independent raw traversal.
func TestRawReference(t *testing.T) {
	var cache Cache
	var w, verifier Workspace
	var seed, cValue, dValue big.Int
	var cert Certificate
	for d := 2; d <= 24; d++ {
		dValue.SetInt64(int64(d))
		for c := 1; c <= 32; c++ {
			cValue.SetInt64(int64(c))
			m, err := NewMap(&cValue, &dValue)
			if err != nil {
				t.Fatal(err)
			}
			for n := 1; n <= 128; n++ {
				seed.SetInt64(int64(n))
				if err = m.Classify(&seed, Limits{1024, 33}, &cache, &w, &cert); err != nil {
					t.Fatalf("c=%d D=%d n=%d: %v", c, d, n, err)
				}
				kind, period, err := ReferenceOutcome(c, d, n)
				if err != nil || kind != cert.Outcome || int64(period) != cert.Period.Int64() {
					t.Fatalf("raw mismatch c=%d D=%d n=%d: %v", c, d, n, err)
				}
				if err = m.Verify(&cert, 1024, &verifier); err != nil {
					t.Fatal(err)
				}
			}
		}
	}
}

// TestFaultInjection rejects changes to the common prefix, return clock, or trace header.
func TestFaultInjection(t *testing.T) {
	m, _ := NewMap(big.NewInt(3), big.NewInt(2))
	var cache Cache
	var w, verifier Workspace
	var cert, altered Certificate
	if err := m.Classify(big.NewInt(10), Limits{32, 4}, &cache, &w, &cert); err != nil {
		t.Fatal(err)
	}
	mutations := []func(*Certificate){
		func(x *Certificate) { x.Seed.SetInt64(0) },
		func(x *Certificate) { x.Phase.Add(&x.Phase, big.NewInt(1)) },
		func(x *Certificate) { x.Clock.Add(&x.Clock, big.NewInt(1)) },
		func(x *Certificate) { x.Period.Add(&x.Period, big.NewInt(1)) },
		func(x *Certificate) { x.Period.SetInt64(0) },
		func(x *Certificate) { x.PrefixBlocks = x.Blocks },
		func(x *Certificate) { x.PrefixBlocks = x.Blocks + 1 },
		func(x *Certificate) { x.Outcome = 0 },
		func(x *Certificate) { x.Blocks = ^uint64(0) },
	}
	for i, mutate := range mutations {
		CopyCertificate(&altered, &cert)
		mutate(&altered)
		if err := m.Verify(&altered, 32, &verifier); err == nil {
			t.Fatalf("accepted mutation %d", i)
		}
	}
	if err := m.Verify(nil, 32, &verifier); err == nil {
		t.Fatal("accepted nil certificate")
	}
}

// TestResourceAndTrap proves zero-budget refusal is not confused with a zero-event true trap.
func TestResourceAndTrap(t *testing.T) {
	m, _ := NewMap(big.NewInt(1), big.NewInt(2))
	var cache Cache
	var w, verifier Workspace
	var cert Certificate
	cert.Seed.SetInt64(77)
	err := m.Classify(big.NewInt(1), Limits{0, 2}, &cache, &w, &cert)
	if !errors.Is(err, ErrResource) || cert.Seed.Int64() != 77 {
		t.Fatal("resource refusal modified output or claimed completion")
	}
	err = m.Classify(big.NewInt(1), Limits{1, 1}, &cache, &w, &cert)
	if !errors.Is(err, ErrResource) {
		t.Fatal("accepted insufficient dense core capacity")
	}
	trapMap, _ := NewMap(big.NewInt(6), big.NewInt(4))
	if err := trapMap.Classify(big.NewInt(1), Limits{}, &cache, &w, &cert); err != nil {
		t.Fatal(err)
	}
	if cert.Outcome != Trap || cert.Blocks != 0 || cert.Clock.Sign() != 0 {
		t.Fatal("initial inaccessible phase was not a zero-event true trap")
	}
	if err := trapMap.Verify(&cert, 0, &verifier); err != nil {
		t.Fatal(err)
	}
	cert.Period.SetInt64(1)
	if err := trapMap.Verify(&cert, 1, &verifier); err == nil {
		t.Fatal("accepted a positive trap return")
	}
}

// TestOwnershipAndHugeClock checks direct input aliases, snapshots, and multiword raw clocks.
func TestOwnershipAndHugeClock(t *testing.T) {
	var c, d big.Int
	c.SetInt64(1)
	d.Lsh(big.NewInt(1), 200)
	m, _ := NewMap(&c, &d)
	var cache Cache
	var w, verifier Workspace
	var cert Certificate
	cert.Seed.SetInt64(1)
	if err := m.Classify(&cert.Seed, Limits{1, 2}, &cache, &w, &cert); err != nil {
		t.Fatal(err)
	}
	if cert.Blocks != 1 || cert.Period.Cmp(&d) != 0 || cert.Period.BitLen() != 201 {
		t.Fatal("huge clock was truncated or normalized away")
	}
	c.SetInt64(0)
	d.SetInt64(0)
	w.state.SetInt64(999)
	w.clock.SetInt64(999)
	cache.clocks[1].SetInt64(999)
	if err := m.Verify(&cert, 1, &verifier); err != nil {
		t.Fatal("certificate or map borrowed mutable input storage:", err)
	}
}

// TestBoundaryAndBasinControls distinguishes access, nonempty cores, and genuine cycles.
func TestBoundaryAndBasinControls(t *testing.T) {
	var cache Cache
	var w Workspace
	var cert Certificate
	for _, pair := range [][2]int64{{9, 6}, {10, 4}, {64, 6}} {
		m, _ := NewMap(big.NewInt(pair[0]), big.NewInt(pair[1]))
		for n := int64(1); n <= 128; n++ {
			err := m.Classify(big.NewInt(n), Limits{512, 65}, &cache, &w, &cert)
			if err != nil || cert.Outcome != Trap {
				t.Fatal("cycle-free control did not reach a true trap", pair, n, err)
			}
		}
	}
	m, _ := NewMap(big.NewInt(6), big.NewInt(4))
	for _, item := range []struct {
		seed int64
		kind Outcome
	}{{2, Periodic}, {4, Trap}} {
		err := m.Classify(big.NewInt(item.seed), Limits{8, 3}, &cache, &w, &cert)
		if err != nil || cert.Outcome != item.kind {
			t.Fatal("initial access was mistaken for basin membership", err)
		}
	}
	for _, pair := range [][2]int64{{0, 2}, {-1, 2}, {1, 1}, {1, -2}} {
		if _, err := NewMap(big.NewInt(pair[0]), big.NewInt(pair[1])); err == nil {
			t.Fatal("accepted invalid map", pair)
		}
	}
	if _, err := NewMap(nil, big.NewInt(2)); err == nil {
		t.Fatal("accepted nil offset")
	}
	var invalid *Map
	if err := invalid.Classify(big.NewInt(1), Limits{1, 2}, &cache, &w, &cert); err == nil {
		t.Fatal("accepted nil map")
	}
	if err := m.Classify(big.NewInt(1), Limits{}, nil, &w, &cert); err == nil {
		t.Fatal("accepted nil cache")
	}
	if err := m.Classify(big.NewInt(1), Limits{}, &cache, nil, &cert); err == nil {
		t.Fatal("accepted nil workspace")
	}
}

// TestUniversalPeriodicity checks the gcd decision and independently owned core getter.
func TestUniversalPeriodicity(t *testing.T) {
	for c := int64(1); c <= 16; c++ {
		for d := int64(2); d <= 12; d++ {
			m, _ := NewMap(big.NewInt(c), big.NewInt(d))
			all, err := m.AllSeedsPeriodic()
			if err != nil || all != (ReferenceGcd(int(c), int(d)) == 1) {
				t.Fatal("universal gcd criterion mismatch", c, d, err)
			}
			var core big.Int
			if err := m.CoreRadius(&core); err != nil || core.Cmp(big.NewInt(c)) > 0 {
				t.Fatal("invalid copied core bound", err)
			}
			core.SetInt64(-1)
			if m.core.Sign() < 0 {
				t.Fatal("core getter exposed mutable map storage")
			}
		}
	}
}

// TestWarmedSmallEventAllocation measures arithmetic reuse on the one-state positive cycle.
func TestWarmedSmallEventAllocation(t *testing.T) {
	m, _ := NewMap(big.NewInt(1), big.NewInt(2))
	var w Workspace
	if err := w.Prepare(m, big.NewInt(1)); err != nil {
		t.Fatal(err)
	}
	allocations := testing.AllocsPerRun(100, func() {
		if err := m.Event(&w); err != nil {
			t.Fatal(err)
		}
	})
	if allocations != 0 {
		t.Fatalf("warmed small event allocated %g objects", allocations)
	}
}

// SameCertificate detects mutations to any owned witness field, not just the seed.
func SameCertificate(a, b *Certificate) bool {
	return a.Seed.Cmp(&b.Seed) == 0 && a.Phase.Cmp(&b.Phase) == 0 &&
		a.Clock.Cmp(&b.Clock) == 0 && a.Period.Cmp(&b.Period) == 0 &&
		a.Blocks == b.Blocks && a.PrefixBlocks == b.PrefixBlocks && a.Outcome == b.Outcome
}

// TestFullRefusalPreservation checks every field on distinct capacity and validation exits.
func TestFullRefusalPreservation(t *testing.T) {
	m, _ := NewMap(big.NewInt(1), big.NewInt(2))
	var cache Cache
	var w Workspace
	var out, original Certificate
	out.Seed.SetInt64(77)
	out.Phase.SetInt64(88)
	out.Clock.SetInt64(99)
	out.Period.SetInt64(111)
	out.Blocks, out.PrefixBlocks, out.Outcome = 7, 6, Periodic
	CopyCertificate(&original, &out)
	cases := []struct {
		name     string
		seed     *big.Int
		limits   Limits
		cache    *Cache
		work     *Workspace
		resource bool
	}{
		{"events", big.NewInt(1), Limits{0, 2}, &cache, &w, true},
		{"core", big.NewInt(1), Limits{1, 1}, &cache, &w, true},
		{"capacity", big.NewInt(1), Limits{1, -1}, &cache, &w, false},
		{"zero", big.NewInt(0), Limits{1, 2}, &cache, &w, false},
		{"nil seed", nil, Limits{1, 2}, &cache, &w, false},
		{"nil cache", big.NewInt(1), Limits{1, 2}, nil, &w, false},
		{"nil workspace", big.NewInt(1), Limits{1, 2}, &cache, nil, false},
	}
	for _, item := range cases {
		err := m.Classify(item.seed, item.limits, item.cache, item.work, &out)
		if err == nil || (item.resource && !errors.Is(err, ErrResource)) ||
			!SameCertificate(&original, &out) {
			t.Fatalf("%s refusal changed the witness or returned the wrong status: %v",
				item.name, err)
		}
	}
	// Each supported input-field alias must also retain all old fields on refusal.
	for _, seed := range []*big.Int{&out.Seed, &out.Phase, &out.Clock, &out.Period} {
		err := m.Classify(seed, Limits{0, 2}, &cache, &w, &out)
		if !errors.Is(err, ErrResource) || !SameCertificate(&original, &out) {
			t.Fatal("aliased refusal changed a certificate field", err)
		}
	}
}

// TestReturnAndFalseTrapControls separates valid nonminimal returns from stopped-clock ghosts.
func TestReturnAndFalseTrapControls(t *testing.T) {
	m, _ := NewMap(big.NewInt(1), big.NewInt(2))
	var w Workspace
	var cert Certificate
	cert.Seed.SetInt64(1)
	cert.Phase.SetInt64(1)
	cert.Period.SetInt64(4)
	cert.Blocks, cert.Outcome = 2, Periodic
	if err := m.Verify(&cert, 2, &w); err != nil {
		t.Fatal("rejected a legal repeated positive return", err)
	}
	cert.Period.SetInt64(0)
	cert.Blocks, cert.Outcome = 0, Trap
	if err := m.Verify(&cert, 0, &w); err == nil {
		t.Fatal("accepted an accessible state as a trap")
	}
	trapMap, _ := NewMap(big.NewInt(6), big.NewInt(4))
	cert.Blocks, cert.PrefixBlocks = 1, 1
	if err := trapMap.Verify(&cert, 1, &w); err == nil {
		t.Fatal("advanced past a stopped inaccessible phase")
	}
}

// TestEveryInputFieldAlias snapshots each direct alias before output storage overwrites it.
func TestEveryInputFieldAlias(t *testing.T) {
	m, _ := NewMap(big.NewInt(1), big.NewInt(2))
	var cache Cache
	var w, verifier Workspace
	var cert Certificate
	fields := []*big.Int{&cert.Seed, &cert.Phase, &cert.Clock, &cert.Period}
	for i, seed := range fields {
		seed.SetInt64(1)
		if err := m.Classify(seed, Limits{1, 2}, &cache, &w, &cert); err != nil {
			t.Fatal("alias classification failed", i, err)
		}
		if cert.Seed.Int64() != 1 || cert.Phase.Int64() != 1 || cert.Clock.Sign() != 0 ||
			cert.Period.Int64() != 2 || cert.Blocks != 1 || cert.PrefixBlocks != 0 ||
			cert.Outcome != Periodic {
			t.Fatal("input alias altered the recovered witness", i)
		}
		if err := m.Verify(&cert, 1, &verifier); err != nil {
			t.Fatal("alias produced an unverifiable certificate", i, err)
		}
	}
}

// TestCacheWidthIsolation stresses changing table sizes and full-word clock ownership.
func TestCacheWidthIsolation(t *testing.T) {
	var cache Cache
	for _, size := range [][2]int{{2, 1}, {6, 4}, {3, 2}, {9, 8}, {2, 1}} {
		entries, words := size[0], size[1]
		if err := cache.Prepare(entries, words); err != nil {
			t.Fatal(err)
		}
		if len(cache.seen) != entries || len(cache.clocks) != entries ||
			len(cache.blocks) != entries || len(cache.words) != entries*words {
			t.Fatal("cache retained a stale active slice length", size)
		}
		for i := 0; i < entries; i++ {
			if cache.seen[i] || cache.clocks[i].Sign() != 0 {
				t.Fatal("cache reuse retained a seen flag or raw clock", size, i)
			}
			cache.clocks[i].SetInt64(int64(i + 1))
			cache.seen[i] = true
			cache.blocks[i] = 7
		}
		// Set the last possible reserved bit, then inspect every other clock independently.
		high := words*bits.UintSize - 1
		for changed := 0; changed < entries; changed++ {
			cache.clocks[changed].SetBit(&cache.clocks[changed], high, 1)
			if cache.clocks[changed].Bit(high) != 1 {
				t.Fatal("clock lost its reserved high word", size, changed)
			}
			var expected big.Int
			for other := 0; other < entries; other++ {
				expected.SetInt64(int64(other + 1))
				if other != changed && cache.clocks[other].Cmp(&expected) != 0 {
					t.Fatal("cache clock backing storage overlapped", size, changed, other)
				}
			}
			cache.clocks[changed].SetInt64(int64(changed + 1))
		}
	}
}

// TestHugeCoreRefusal verifies a short witness even when dense classification is infeasible.
func TestHugeCoreRefusal(t *testing.T) {
	c := new(big.Int).Lsh(big.NewInt(1), 200)
	c.Sub(c, big.NewInt(1))
	m, err := NewMap(c, big.NewInt(2))
	if err != nil {
		t.Fatal(err)
	}
	var cache Cache
	var w, verifier Workspace
	var out, original, supplied Certificate
	out.Seed.SetInt64(77)
	out.Phase.SetInt64(88)
	out.Clock.SetInt64(99)
	out.Period.SetInt64(111)
	out.Blocks, out.PrefixBlocks, out.Outcome = 7, 6, Periodic
	CopyCertificate(&original, &out)
	err = m.Classify(c, Limits{1, 2}, &cache, &w, &out)
	if !errors.Is(err, ErrResource) || !SameCertificate(&original, &out) {
		t.Fatal("huge numeric core was truncated or modified a refused output", err)
	}
	supplied.Seed.Set(c)
	supplied.Phase.Set(c)
	supplied.Period.SetInt64(2)
	supplied.Blocks, supplied.Outcome = 1, Periodic
	if err := m.Verify(&supplied, 1, &verifier); err != nil {
		t.Fatal("cache-independent verification refused a short huge-state witness", err)
	}
}
