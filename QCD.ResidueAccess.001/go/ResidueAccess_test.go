// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere
//
// Tests for the residue-access certificate. Reference values are recomputed
// with math/big routes that do not share code with the sweeps under test,
// except where a test explicitly says it exercises the production helper.

package main

import (
	"math/big"
	"testing"
)

// referenceRepunit returns 1 + q + ... + q^(j-1) by summation of powers, an
// independent route to the running-product helper used by the sweeps.
func referenceRepunit(q, j uint64) *big.Int {
	sum := new(big.Int)
	power := big.NewInt(1)
	base := new(big.Int).SetUint64(q)
	for i := uint64(0); i < j; i++ {
		sum.Add(sum, power)
		power.Mul(power, base)
	}
	return sum
}

// referenceOrbit returns the residue orbit of zero by matrix-free iteration.
func referenceOrbit(q, c, D, j uint64) uint64 {
	r := uint64(0)
	for i := uint64(0); i < j; i++ {
		r = (q*r + c) % D
	}
	return r
}

// referenceModulus computes D*(q-1)/gcd(c, D*(q-1)) without the production
// helper.
func referenceModulus(q, c, D uint64) uint64 {
	top := new(big.Int).Mul(big.NewInt(int64(D)), big.NewInt(int64(q-1)))
	g := new(big.Int).GCD(nil, nil, big.NewInt(int64(c)), top)
	quot := new(big.Int).Quo(top, g)
	return quot.Uint64()
}

// TestOrbitFormulaMatchesReference checks the closed form against the walked
// orbit on a rectangle around the sweep bounds.
func TestOrbitFormulaMatchesReference(t *testing.T) {
	cases := 0
	for q := uint64(2); q <= 12; q++ {
		for c := uint64(1); c <= 6; c++ {
			for D := uint64(2); D <= 12; D++ {
				for j := uint64(0); j <= 12; j++ {
					sum := referenceRepunit(q, j)
					sum.Mul(sum, new(big.Int).SetUint64(c))
					sum.Mod(sum, new(big.Int).SetUint64(D))
					if sum.Uint64() != referenceOrbit(q, c, D, j) {
						t.Fatalf("formula q=%d c=%d D=%d j=%d: %v", q, c, D, j, sum)
					}
					cases++
				}
			}
		}
	}
	if cases == 0 {
		t.Fatal("no cases checked")
	}
}

// TestCriterionMatchesReference checks that the orbit of zero returns exactly
// when the access modulus divides q^j - 1.
func TestCriterionMatchesReference(t *testing.T) {
	for q := uint64(2); q <= 12; q++ {
		for c := uint64(1); c <= 6; c++ {
			for D := uint64(2); D <= 12; D++ {
				M := referenceModulus(q, c, D)
				for j := uint64(1); j <= 12; j++ {
					power := new(big.Int).Exp(new(big.Int).SetUint64(q),
						new(big.Int).SetUint64(j), nil)
					power.Sub(power, big.NewInt(1))
					rem := new(big.Int).Mod(power, new(big.Int).SetUint64(M))
					want := rem.Sign() == 0
					got := referenceOrbit(q, c, D, j) == 0
					if got != want {
						t.Fatalf("criterion q=%d c=%d D=%d j=%d: orbit %v, modulus %v",
							q, c, D, j, got, want)
					}
				}
			}
		}
	}
}

// TestOrderIsMinimal checks that the orbit return time is the least exponent
// with q^m = 1 modulo the access modulus, and that it never exceeds D.
func TestOrderIsMinimal(t *testing.T) {
	for q := uint64(2); q <= 20; q++ {
		for c := uint64(1); c <= 6; c++ {
			for D := uint64(2); D <= 20; D++ {
				if Gcd(q, D) != 1 {
					continue
				}
				M := referenceModulus(q, c, D)
				m := uint64(0)
				for j := uint64(1); j <= M+1 && m == 0; j++ {
					power := new(big.Int).Exp(new(big.Int).SetUint64(q),
						new(big.Int).SetUint64(j), nil)
					power.Sub(power, big.NewInt(1))
					if new(big.Int).Mod(power, new(big.Int).SetUint64(M)).Sign() == 0 {
						m = j
					}
				}
				if m == 0 {
					t.Fatalf("no order found q=%d c=%d D=%d M=%d", q, c, D, M)
				}
				if m > D {
					t.Fatalf("order exceeds D q=%d c=%d D=%d M=%d m=%d", q, c, D, M, m)
				}
				if referenceOrbit(q, c, D, m) != 0 {
					t.Fatalf("orbit not returned at the order q=%d c=%d D=%d m=%d", q, c, D, m)
				}
				for j := uint64(1); j < m; j++ {
					if referenceOrbit(q, c, D, j) == 0 {
						t.Fatalf("early return q=%d c=%d D=%d j=%d", q, c, D, j)
					}
				}
			}
		}
	}
}

// TestTrapResidueModuloThree checks the example with an unreachable fixed
// residue: modulo three with multiplier two and offset one, residue two is a
// fixed point of the residue map and the orbit of zero never visits it.
func TestTrapResidueModuloThree(t *testing.T) {
	if got := AccessStepU64(2, 1, 3, 2); got != 2 {
		t.Fatalf("residue two should be fixed, got %d", got)
	}
	for j := uint64(0); j <= 20; j++ {
		if got := referenceOrbit(2, 1, 3, j); got == 2 {
			t.Fatalf("orbit reached the trap at j=%d", j)
		}
	}
	if referenceOrbit(2, 1, 3, 1) != 1 || referenceOrbit(2, 1, 3, 2) != 0 {
		t.Fatal("access cycle modulo three is not zero, one")
	}
}

// TestPrimeFullAccessExhausts checks the exhaustion statement at a prime where
// the multiplier is one: the orbit of zero visits every residue.
func TestPrimeFullAccessExhausts(t *testing.T) {
	primes := []uint64{2, 3, 5, 7, 11}
	for _, p := range primes {
		for q := uint64(2); q <= 30; q++ {
			if Gcd(q, p) != 1 || (q-1)%p != 0 {
				continue
			}
			for c := uint64(1); c < p; c++ {
				seen := OrbitSetU64(q, c, p, p)
				for r := uint64(0); r < p; r++ {
					if !seen[r] {
						t.Fatalf("residue %d unreached p=%d q=%d c=%d", r, p, q, c)
					}
				}
			}
		}
	}
}

// TestPrimeNonOneMissesResidues checks the necessity direction at a prime
// where the multiplier is not one: the orbit is shorter than the prime and
// leaves exactly p - m residues unreached.
func TestPrimeNonOneMissesResidues(t *testing.T) {
	primes := []uint64{3, 5, 7, 11}
	for _, p := range primes {
		for q := uint64(2); q <= 30; q++ {
			if Gcd(q, p) != 1 || (q-1)%p == 0 {
				continue
			}
			for c := uint64(1); c < p; c++ {
				M := referenceModulus(q, c, p)
				m := uint64(0)
				for j := uint64(1); j <= p && m == 0; j++ {
					power := new(big.Int).Exp(new(big.Int).SetUint64(q),
						new(big.Int).SetUint64(j), nil)
					power.Sub(power, big.NewInt(1))
					if new(big.Int).Mod(power, new(big.Int).SetUint64(M)).Sign() == 0 {
						m = j
					}
				}
				if m == 0 || m >= p {
					t.Fatalf("expected a short return p=%d q=%d c=%d m=%d", p, q, c, m)
				}
				seen := OrbitSetU64(q, c, p, m)
				unreached := uint64(0)
				for r := uint64(0); r < p; r++ {
					if !seen[r] {
						unreached++
					}
				}
				if unreached != p-m {
					t.Fatalf("unreached %d, want %d p=%d q=%d c=%d", unreached, p-m, p, q, c)
				}
			}
		}
	}
}

// TestExamplesAndSliceValues checks the worked examples and the slice with
// multiplier D - 1, whose return time is two for every offset not divisible
// by D.
func TestExamplesAndSliceValues(t *testing.T) {
	values := []struct {
		q, c, D, j, want uint64
	}{
		{2, 1, 3, 0, 0}, {2, 1, 3, 1, 1}, {2, 1, 3, 2, 0},
		{2, 1, 7, 1, 1}, {2, 1, 7, 2, 3}, {2, 1, 7, 3, 0},
		{2, 1, 15, 1, 1}, {2, 1, 15, 2, 3}, {2, 1, 15, 3, 7}, {2, 1, 15, 4, 0},
		{3, 1, 13, 1, 1}, {3, 1, 13, 2, 4}, {3, 1, 13, 3, 0},
		{3, 1, 2, 1, 1}, {3, 1, 2, 2, 0},
		{2, 7, 3, 1, 1}, {2, 7, 3, 2, 0},
	}
	for _, v := range values {
		if got := referenceOrbit(v.q, v.c, v.D, v.j); got != v.want {
			t.Fatalf("orbit q=%d c=%d D=%d j=%d: got %d want %d",
				v.q, v.c, v.D, v.j, got, v.want)
		}
	}
	for D := uint64(3); D <= 13; D++ {
		for c := uint64(1); c < D; c++ {
			q := D - 1
			if referenceOrbit(q, c, D, 1) == 0 {
				t.Fatalf("early return q=%d c=%d D=%d", q, c, D)
			}
			if referenceOrbit(q, c, D, 2) != 0 {
				t.Fatalf("no return at two q=%d c=%d D=%d", q, c, D)
			}
		}
	}
}

// TestSweepTotals pins the per-slice certificate counts and the total, so a
// silent change of bounds or of a sweep body fails the test.
func TestSweepTotals(t *testing.T) {
	formula := sweepFormula()
	if formula.Checks != 133308 || formula.Failures != 0 {
		t.Fatalf("formula slice: %d checks, %d failures", formula.Checks, formula.Failures)
	}
	criterion := sweepCriterion()
	if criterion.Checks != 126960 || criterion.Failures != 0 {
		t.Fatalf("criterion slice: %d checks, %d failures", criterion.Checks, criterion.Failures)
	}
	order := sweepOrder()
	if order.Checks != 103467 || order.Failures != 0 {
		t.Fatalf("order slice: %d checks, %d failures", order.Checks, order.Failures)
	}
	full := sweepFullAccess()
	if full.Checks != 1433 || full.Failures != 0 {
		t.Fatalf("full-access slice: %d checks, %d failures", full.Checks, full.Failures)
	}
	nonone := sweepPrimeNonOne()
	if nonone.Checks != 2044 || nonone.Failures != 0 {
		t.Fatalf("prime non-one slice: %d checks, %d failures", nonone.Checks, nonone.Failures)
	}
	examples := sweepExamples()
	if examples.Checks != 88 || examples.Failures != 0 {
		t.Fatalf("example slice: %d checks, %d failures", examples.Checks, examples.Failures)
	}
	total := formula.Checks + criterion.Checks + order.Checks + full.Checks +
		nonone.Checks + examples.Checks
	if total != 367300 {
		t.Fatalf("total %d, want 367300", total)
	}
}

// TestDocumentedRanges checks the bounds the documents quote and the
// arithmetic headroom they rely on: every product q*D + c in the sweeps stays
// far below two to the fifty-eighth.
func TestDocumentedRanges(t *testing.T) {
	if accessMaxQ != 24 || accessMaxC != 12 || accessMaxD != 24 || accessMaxJ != 20 {
		t.Fatal("rectangle bounds changed from the documented ones")
	}
	if accessPrimeQ != 40 {
		t.Fatal("prime multiplier bound changed from the documented one")
	}
	const guard = uint64(1) << 58
	if got := uint64(accessMaxQ*accessMaxD + accessMaxC); got >= guard {
		t.Fatalf("rectangle product %d reaches the guard", got)
	}
	if got := uint64(accessPrimeQ*13 + 13); got >= guard {
		t.Fatalf("prime product %d reaches the guard", got)
	}
}

// TestWarmedOrbitAllocation checks that walking the orbit reuses its buffers:
// after warm-up the step loop allocates nothing.
func TestWarmedOrbitAllocation(t *testing.T) {
	warm := referenceOrbit(23, 11, 24, 20)
	if warm == 24 {
		t.Fatal("reference orbit left the residue range")
	}
	allocs := testing.AllocsPerRun(100, func() {
		if got := AccessOrbitU64(23, 11, 24, 20); got != warm {
			t.Fatalf("orbit changed: %d", got)
		}
	})
	if allocs != 0 {
		t.Fatalf("orbit walk allocated %v values per run", allocs)
	}
}
