// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"errors"
	"fmt"
	"math/big"
	"strings"
	"sync"
	"testing"
)

// Reference records an independently extracted raw cycle at its minimum division endpoint.
type Reference struct {
	representatives []int
	period          int
}

// ReferenceWorkspace reuses bounded raw graph storage across parameter cells.
type ReferenceWorkspace struct {
	visited               []bool
	stamp, position, path []int
}

// GCD computes the reference arithmetic without using the certificate implementation.
func GCD(a, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// ReferenceCofactor removes prime factors using trial division, not the implementation's gcd loop.
func ReferenceCofactor(c, d int) (int, int) {
	cofactor := c
	for prime := 2; prime <= d; prime++ {
		if d%prime != 0 {
			continue
		}
		for cofactor%prime == 0 {
			cofactor /= prime
		}
	}
	return c / cofactor, cofactor
}

// RawStep applies division precedence directly in the bounded reference arithmetic.
func RawStep(n, c, d int) int {
	if n%d == 0 {
		return n / d
	}
	return n + c
}

// Prepare resets the graph arrays before hot path traversal.
func (w *ReferenceWorkspace) Prepare(n int) {
	if cap(w.visited) < n+1 {
		w.visited = make([]bool, n+1)
		w.stamp = make([]int, n+1)
		w.position = make([]int, n+1)
		w.path = make([]int, n)
	} else {
		w.visited = w.visited[:n+1]
		w.stamp = w.stamp[:n+1]
		w.position = w.position[:n+1]
		w.path = w.path[:n]
		clear(w.visited)
		clear(w.stamp)
	}
}

// ReferenceCycles exhausts raw cycles in 1..cD, independently of the modular enumeration.
// The universal window theorem places every raw cycle inside this box; the test is finite.
func ReferenceCycles(c, d int, w *ReferenceWorkspace) ([]Reference, error) {
	bound := c * d
	w.Prepare(bound)
	visited, stamp := w.visited[:bound+1], w.stamp[:bound+1]
	position, path := w.position[:bound+1], w.path[:bound]
	supported, _ := ReferenceCofactor(c, d)
	result := make([]Reference, 0, c)
	for seed := 1; seed <= bound; seed++ {
		if visited[seed] {
			continue
		}
		n, length := seed, 0
		for n > 0 && n <= bound && !visited[n] {
			visited[n], stamp[n], position[n] = true, seed, length
			path[length] = n
			length++
			n = RawStep(n, c, d)
		}
		if n <= 0 || n > bound || stamp[n] != seed {
			continue
		}
		cycle := path[position[n]:length]
		cycle = cycle[:len(cycle)]
		phases := make([]int, 0, len(cycle))
		// A phase is a division destination, determined from the preceding raw instruction.
		for i, value := range cycle {
			previous := i - 1
			if previous < 0 {
				previous = len(cycle) - 1
			}
			if cycle[previous]%d != 0 {
				continue
			}
			if value > c || value%supported != 0 {
				return nil, errors.New("raw cycle violates endpoint or supported-factor bound")
			}
			phases = append(phases, value/supported)
		}
		if len(phases) == 0 {
			return nil, errors.New("positive raw cycle has no division")
		}
		minimum := 0
		for i := range phases {
			if phases[i] < phases[minimum] {
				minimum = i
			}
		}
		canonical := make([]int, len(phases))
		for i := range phases {
			canonical[i] = phases[(minimum+i)%len(phases)]
		}
		result = append(result, Reference{canonical, len(cycle)})
	}
	return result, nil
}

// ReferenceKey makes the canonical reference orbit suitable for set comparison.
func ReferenceKey(representatives []int) string {
	var key strings.Builder
	for _, value := range representatives {
		fmt.Fprintf(&key, "%d,", value)
	}
	return key.String()
}

// CertificateKey encodes the same orbit from arbitrary-precision representatives.
func CertificateKey(certificate *Certificate) string {
	var key strings.Builder
	for i := range certificate.Representatives {
		key.WriteString(certificate.Representatives[i].String())
		key.WriteByte(',')
	}
	return key.String()
}

// ReferenceOrder scans the effective unit modulus, including its singleton case.
func ReferenceOrder(d, modulus int) int {
	if modulus == 1 {
		return 1
	}
	value := d % modulus
	for order := 1; order <= modulus; order++ {
		if value == 1 {
			return order
		}
		value = value * d % modulus
	}
	return 0
}

// CheckReferenceChunk compares independently extracted raw cycles against every certificate.
func CheckReferenceChunk(first, last int) error {
	var cache Cache
	var w Workspace
	var referenceWorkspace ReferenceWorkspace
	var c, d big.Int
	for divisor := first; divisor < last; divisor++ {
		d.SetInt64(int64(divisor))
		for offset := 1; offset <= 96; offset++ {
			c.SetInt64(int64(offset))
			m, err := NewMap(&c, &d)
			if err != nil {
				return err
			}
			s, cofactor := ReferenceCofactor(offset, divisor)
			window := cofactor * (divisor/GCD(offset, divisor) - 1) / (divisor - 1)
			if m.s.Int64() != int64(s) || m.t.Int64() != int64(cofactor) ||
				m.window.Int64() != int64(window) {
				return fmt.Errorf("c=%d D=%d: decomposition differs", offset, divisor)
			}
			references, err := ReferenceCycles(offset, divisor, &referenceWorkspace)
			if err != nil {
				return err
			}
			expected := make(map[string]int, len(references))
			for _, cycle := range references {
				expected[ReferenceKey(cycle.representatives)] = cycle.period
			}
			report, err := m.Enumerate(96, &cache, &w, func(cert *Certificate) error {
				if err := m.Verify(cert, &w); err != nil {
					return err
				}
				key := CertificateKey(cert)
				period, found := expected[key]
				if !found || cert.RawPeriod.Int64() != int64(period) {
					return fmt.Errorf("raw cycle or period mismatch: %s", key)
				}
				delete(expected, key)
				first := int(cert.Representatives[0].Int64())
				modulus := cofactor / GCD(first, cofactor)
				if cert.OrderModulus.Int64() != int64(modulus) ||
					cert.HPeriod.Int64() != int64(ReferenceOrder(divisor, modulus)) {
					return errors.New("effective modulus or independently scanned order differs")
				}
				return nil
			})
			if err != nil || !report.Complete || len(expected) != 0 ||
				report.Cycles != uint64(len(references)) {
				return fmt.Errorf("c=%d D=%d: comparison failed: %v", offset, divisor, err)
			}
			if !report.EmptyWindow && report.Visited != uint64(cofactor) {
				return errors.New("complete traversal did not visit every modular representative")
			}
		}
	}
	return nil
}

// TestBoundedReference covers all 4512 parameter pairs with four independent chunks.
func TestBoundedReference(t *testing.T) {
	var group sync.WaitGroup
	var failures [4]error
	bounds := [5]int{2, 14, 26, 38, 49}
	for i := range failures {
		group.Add(1)
		go func(i int) {
			defer group.Done()
			failures[i] = CheckReferenceChunk(bounds[i], bounds[i+1])
		}(i)
	}
	group.Wait()
	for _, failure := range failures {
		if failure != nil {
			t.Fatal(failure)
		}
	}
}

// MakeMap builds small independent test parameters.
func MakeMap(t *testing.T, c, d int64) *Map {
	t.Helper()
	m, err := NewMap(big.NewInt(c), big.NewInt(d))
	if err != nil {
		t.Fatal(err)
	}
	return m
}

// Representatives initializes owned integer storage for test inputs.
func Representatives(values ...int64) []big.Int {
	result := make([]big.Int, len(values))
	for i, value := range values {
		result[i].SetInt64(value)
	}
	return result
}

// MakeCertificate prepares a checked test certificate with independent storage.
func MakeCertificate(t *testing.T, m *Map, values ...int64) Certificate {
	t.Helper()
	var certificate Certificate
	var w Workspace
	if err := m.BuildCycle(&certificate, Representatives(values...), &w); err != nil {
		t.Fatal(err)
	}
	return certificate
}

// TestGuardsAndGroupedClock checks cancellation, immediate divisions, ghosts, and whole orbits.
func TestGuardsAndGroupedClock(t *testing.T) {
	m := MakeMap(t, 5, 2)
	certificate := MakeCertificate(t, m, 1, 3, 4, 2)
	if certificate.HPeriod.Int64() != 4 || certificate.RawPeriod.Int64() != 6 {
		t.Fatal("grouped period or immediate division count differs")
	}
	var w Workspace
	var dst Certificate
	for _, bad := range [][]big.Int{
		Representatives(1, 3, 4), Representatives(1, 3, 3, 4, 2),
		Representatives(1, 3, 4, 2, 1, 3, 4, 2), Representatives(3, 4, 2, 1),
		Representatives(0), Representatives(-1), Representatives(6), nil,
	} {
		if err := m.BuildCycle(&dst, bad, &w); err == nil {
			t.Fatal("malformed, nonprimitive, or noncanonical cycle accepted")
		}
	}
	ghost := MakeMap(t, 10, 6)
	if err := ghost.BuildCycle(&dst, Representatives(3), &w); err == nil {
		t.Fatal("noncoprime scaling ghost accepted")
	}
	for _, value := range []int64{1, 2} {
		cert := MakeCertificate(t, ghost, value)
		if cert.RawPeriod.Int64() != value+1 {
			t.Fatal("filtered noncoprime clock differs")
		}
	}
	partial := MakeMap(t, 10, 4)
	var cache Cache
	report, err := partial.Enumerate(5, &cache, &w, func(*Certificate) error {
		t.Fatal("a partly surviving orbit was emitted")
		return nil
	})
	if err != nil || !report.Complete || report.Visited != 5 || report.Cycles != 0 {
		t.Fatal("whole-orbit filtering failed", report, err)
	}
	empty := MakeMap(t, 8, 6)
	report, err = empty.Enumerate(0, &cache, &w, func(*Certificate) error {
		t.Fatal("empty window invoked callback despite its nonempty core")
		return nil
	})
	if err != nil || !report.Complete || !report.EmptyWindow || report.Cycles != 0 {
		t.Fatal("nonempty core was confused with a nonempty cycle window", report, err)
	}
	zero := MakeCertificate(t, MakeMap(t, 5, 6), 5)
	if zero.OrderModulus.Int64() != 1 || zero.HPeriod.Int64() != 1 ||
		zero.RawPeriod.Int64() != 6 {
		t.Fatal("positive zero-residue representative was lost")
	}
}

// TestTampering checks all exposed fields and verifies that checking never mutates inputs.
func TestTampering(t *testing.T) {
	m := MakeMap(t, 5, 2)
	original := MakeCertificate(t, m, 1, 3, 4, 2)
	for field := 0; field < 5; field++ {
		var bad Certificate
		if err := bad.CopyFrom(&original); err != nil {
			t.Fatal(err)
		}
		switch field {
		case 0:
			bad.Representatives[1].Add(&bad.Representatives[1], big.NewInt(1))
		case 1:
			bad.HPeriod.Add(&bad.HPeriod, big.NewInt(1))
		case 2:
			bad.RawPeriod.Add(&bad.RawPeriod, big.NewInt(1))
		case 3:
			bad.OrderModulus.Add(&bad.OrderModulus, big.NewInt(1))
		case 4:
			bad.Representatives = bad.Representatives[:0]
		}
		before := fmt.Sprintf("%s/%s/%s/%s", CertificateKey(&bad), bad.HPeriod.String(),
			bad.RawPeriod.String(), bad.OrderModulus.String())
		var w Workspace
		if err := m.Verify(&bad, &w); err == nil {
			t.Fatal("tampered certificate accepted")
		}
		after := fmt.Sprintf("%s/%s/%s/%s", CertificateKey(&bad), bad.HPeriod.String(),
			bad.RawPeriod.String(), bad.OrderModulus.String())
		if before != after {
			t.Fatal("verification modified its certificate")
		}
	}
}

// TestOwnershipAndAliases checks constructor copies, input snapshots, and owned output retention.
func TestOwnershipAndAliases(t *testing.T) {
	c, d := big.NewInt(10), big.NewInt(6)
	m, err := NewMap(c, d)
	if err != nil {
		t.Fatal(err)
	}
	c.SetInt64(0)
	d.SetInt64(0)
	input := Representatives(1)
	var certificate Certificate
	var w Workspace
	if err := m.BuildCycle(&certificate, input, &w); err != nil {
		t.Fatal(err)
	}
	input[0].SetInt64(999)
	if certificate.Representatives[0].Int64() != 1 {
		t.Fatal("certificate shares input storage")
	}
	if err := m.BuildCycle(&certificate, certificate.Representatives, &w); err != nil {
		t.Fatal("direct output/input alias failed", err)
	}
	var copy Certificate
	if err := copy.CopyFrom(&certificate); err != nil {
		t.Fatal(err)
	}
	certificate.Representatives[0].SetInt64(2)
	if copy.Representatives[0].Int64() != 1 {
		t.Fatal("retained certificate shares output storage")
	}
	var supported, cofactor, window big.Int
	if err := m.Decomposition(&supported, &cofactor, &window); err != nil {
		t.Fatal(err)
	}
	if supported.Int64() != 2 || cofactor.Int64() != 5 || window.Int64() != 2 {
		t.Fatal("decomposition output differs")
	}
	cofactor.SetInt64(0)
	if m.t.Int64() != 5 {
		t.Fatal("decomposition exposes map storage")
	}
	if err := m.Decomposition(&supported, &supported, &window); err == nil {
		t.Fatal("ambiguous decomposition destinations accepted")
	}
	state := big.NewInt(1)
	if err := m.RawState(state, state); err != nil || state.Int64() != 2 {
		t.Fatal("direct lifted-state alias failed", err)
	}
	var cache Cache
	retained := make([]Certificate, 0, 2)
	report, err := m.Enumerate(5, &cache, &w, func(cert *Certificate) error {
		var saved Certificate
		if err := saved.CopyFrom(cert); err != nil {
			return err
		}
		retained = append(retained, saved)
		return nil
	})
	if err != nil || !report.Complete || len(retained) != 2 ||
		retained[0].Representatives[0].Int64() != 1 ||
		retained[1].Representatives[0].Int64() != 2 {
		t.Fatal("borrowed callback retention failed", report, err)
	}
}

// TestLargeClocksAndBudgets separates enormous arithmetic from finite enumeration capacity.
func TestLargeClocksAndBudgets(t *testing.T) {
	one := big.NewInt(1)
	divisor := new(big.Int).Lsh(one, 200)
	m, err := NewMap(one, divisor)
	if err != nil {
		t.Fatal(err)
	}
	certificate := MakeCertificate(t, m, 1)
	if certificate.RawPeriod.Cmp(divisor) != 0 || certificate.RawPeriod.IsUint64() {
		t.Fatal("large raw clock was narrowed")
	}
	var cache Cache
	var w Workspace
	large := new(big.Int).Lsh(one, 100)
	large.Add(large, one)
	nonempty, err := NewMap(large, big.NewInt(2))
	if err != nil {
		t.Fatal(err)
	}
	report, err := nonempty.Enumerate(96, &cache, &w, func(*Certificate) error {
		t.Fatal("over-budget search invoked callback")
		return nil
	})
	if !errors.Is(err, ErrEnumerationBudget) || report.Complete || report.Visited != 0 {
		t.Fatal("capacity refusal was reported as an exhaustive answer", report, err)
	}
	supported := new(big.Int).Lsh(one, 300)
	offset := new(big.Int).Mul(supported, large)
	largeDivisor := new(big.Int).Lsh(one, 301)
	empty, err := NewMap(offset, largeDivisor)
	if err != nil {
		t.Fatal(err)
	}
	report, err = empty.Enumerate(0, &cache, &w, func(*Certificate) error {
		t.Fatal("empty window invoked callback")
		return nil
	})
	if err != nil || !report.Complete || !report.EmptyWindow || report.Visited != 0 ||
		report.Cofactor.Cmp(large) != 0 {
		t.Fatal("huge empty window was not certified algebraically", report, err)
	}
	abort := errors.New("callback stopped")
	report, err = MakeMap(t, 5, 2).Enumerate(5, &cache, &w,
		func(*Certificate) error { return abort })
	if !errors.Is(err, abort) || report.Complete || report.Cycles != 0 {
		t.Fatal("interrupted callback was reported as complete", report, err)
	}
}

// TestValidation exercises nil and uninitialized public entry points before dereferencing storage.
func TestValidation(t *testing.T) {
	for _, pair := range [][2]*big.Int{
		{nil, big.NewInt(2)}, {big.NewInt(1), nil}, {big.NewInt(0), big.NewInt(2)},
		{big.NewInt(-1), big.NewInt(2)}, {big.NewInt(1), big.NewInt(1)},
		{big.NewInt(1), big.NewInt(-2)},
	} {
		if _, err := NewMap(pair[0], pair[1]); err == nil {
			t.Fatal("invalid parameters accepted")
		}
	}
	var w Workspace
	var cache Cache
	var certificate Certificate
	for _, m := range []*Map{nil, new(Map)} {
		if m.Validate() == nil || m.BuildCycle(&certificate, Representatives(1), &w) == nil ||
			m.Verify(&certificate, &w) == nil || m.Compute(Representatives(1), &w) == nil ||
			m.RawState(big.NewInt(0), big.NewInt(1)) == nil {
			t.Fatal("uninitialized map accepted")
		}
		if _, err := m.Enumerate(1, &cache, &w, func(*Certificate) error { return nil }); err == nil {
			t.Fatal("uninitialized enumeration accepted")
		}
	}
	m := MakeMap(t, 1, 2)
	if m.BuildCycle(nil, Representatives(1), &w) == nil ||
		m.BuildCycle(&certificate, Representatives(1), nil) == nil ||
		m.Verify(nil, &w) == nil || m.Verify(&certificate, nil) == nil ||
		m.Compute(Representatives(1), nil) == nil || m.RawState(nil, big.NewInt(1)) == nil ||
		m.Decomposition(nil, big.NewInt(0), big.NewInt(0)) == nil {
		t.Fatal("nil buffer accepted")
	}
	for _, budget := range []int{-1, 0} {
		_, err := m.Enumerate(budget, &cache, &w, func(*Certificate) error { return nil })
		if err == nil {
			t.Fatal("invalid or insufficient enumeration budget accepted")
		}
	}
	if _, err := m.Enumerate(1, nil, &w, func(*Certificate) error { return nil }); err == nil {
		t.Fatal("nil enumeration cache accepted")
	}
	if _, err := m.Enumerate(1, &cache, &w, nil); err == nil {
		t.Fatal("nil callback accepted")
	}
	if certificate.CopyFrom(nil) == nil {
		t.Fatal("nil certificate source accepted")
	}
}
