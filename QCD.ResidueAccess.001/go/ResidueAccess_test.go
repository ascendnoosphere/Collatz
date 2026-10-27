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

// ReferenceRepunit returns 1 + q + ... + q^(j-1) by summation of powers, an
// independent route to the running-product helper used by the sweeps.
func ReferenceRepunit(q, j uint64) *big.Int {
	sum := new(big.Int)
	power := big.NewInt(1)
	base := new(big.Int).SetUint64(q)
	for i := uint64(0); i < j; i++ {
		sum.Add(sum, power)
		power.Mul(power, base)
	}
	return sum
}

// ReferenceOrbit returns the residue orbit of zero by matrix-free iteration.
func ReferenceOrbit(q, c, D, j uint64) uint64 {
	r := uint64(0)
	for i := uint64(0); i < j; i++ {
		r = (q*r + c) % D
	}
	return r
}

// ReferenceModulus computes D*(q-1)/gcd(c, D*(q-1)) without the production
// helper.
func ReferenceModulus(q, c, D uint64) uint64 {
	top := new(big.Int).Mul(big.NewInt(int64(D)), big.NewInt(int64(q-1)))
	g := new(big.Int).GCD(nil, nil, big.NewInt(int64(c)), top)
	quot := new(big.Int).Quo(top, g)
	return quot.Uint64()
}

// TestOrbitFormulaMatchesReference checks the closed form against the walked
// orbit on a rectangle around the sweep bounds.
func TestOrbitFormulaMatchesReference(t *testing.T) {
	work := NewWorkspace()
	cases := 0
	for q := uint64(2); q <= 12; q++ {
		for c := uint64(1); c <= 6; c++ {
			for D := uint64(2); D <= 12; D++ {
				for j := uint64(0); j <= 12; j++ {
					sum := ReferenceRepunit(q, j)
					sum.Mul(sum, new(big.Int).SetUint64(c))
					sum.Mod(sum, new(big.Int).SetUint64(D))
					if sum.Uint64() != ReferenceOrbit(q, c, D, j) {
						t.Fatalf("formula q=%d c=%d D=%d j=%d: %v", q, c, D, j, sum)
					}
					if got := AccessOrbitU64(q, c, D, j); got != ReferenceOrbit(q, c, D, j) {
						t.Fatalf("production orbit q=%d c=%d D=%d j=%d: %d", q, c, D, j, got)
					}
					if exact := RepunitSumBig(work, q, j); exact.Cmp(ReferenceRepunit(q, j)) != 0 {
						t.Fatalf("production repunit q=%d j=%d: %v", q, j, exact)
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
				M := ReferenceModulus(q, c, D)
				if got := AccessModulusU64(q, c, D); got != M {
					t.Fatalf("production modulus q=%d c=%d D=%d: %d want %d", q, c, D, got, M)
				}
				if got := ModulusByPowers(q, c, D); got != M {
					t.Fatalf("modulus route q=%d c=%d D=%d: %d want %d", q, c, D, got, M)
				}
				for j := uint64(1); j <= 12; j++ {
					power := new(big.Int).Exp(new(big.Int).SetUint64(q),
						new(big.Int).SetUint64(j), nil)
					power.Sub(power, big.NewInt(1))
					rem := new(big.Int).Mod(power, new(big.Int).SetUint64(M))
					want := rem.Sign() == 0
					got := ReferenceOrbit(q, c, D, j) == 0
					if got != want {
						t.Fatalf("criterion q=%d c=%d D=%d j=%d: orbit %v, modulus %v",
							q, c, D, j, got, want)
					}
					if prod := AccessOrbitU64(q, c, D, j) == 0; prod != got {
						t.Fatalf("production criterion q=%d c=%d D=%d j=%d: %v want %v",
							q, c, D, j, prod, got)
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
				M := ReferenceModulus(q, c, D)
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
				work := NewWorkspace()
				if pm, found := LeastOrderBig(work, q, M, 1000); !found || pm != m {
					t.Fatalf("production order q=%d c=%d D=%d: %d/%v want %d",
						q, c, D, pm, found, m)
				}
				if m > D {
					t.Fatalf("order exceeds D q=%d c=%d D=%d M=%d m=%d", q, c, D, M, m)
				}
				if ReferenceOrbit(q, c, D, m) != 0 {
					t.Fatalf("orbit not returned at the order q=%d c=%d D=%d m=%d", q, c, D, m)
				}
				for j := uint64(1); j < m; j++ {
					if ReferenceOrbit(q, c, D, j) == 0 {
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
		if got := ReferenceOrbit(2, 1, 3, j); got == 2 {
			t.Fatalf("orbit reached the trap at j=%d", j)
		}
	}
	if ReferenceOrbit(2, 1, 3, 1) != 1 || ReferenceOrbit(2, 1, 3, 2) != 0 {
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
				M := ReferenceModulus(q, c, p)
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
		if got := ReferenceOrbit(v.q, v.c, v.D, v.j); got != v.want {
			t.Fatalf("orbit q=%d c=%d D=%d j=%d: got %d want %d",
				v.q, v.c, v.D, v.j, got, v.want)
		}
		if got := AccessOrbitU64(v.q, v.c, v.D, v.j); got != v.want {
			t.Fatalf("production orbit q=%d c=%d D=%d j=%d: got %d want %d",
				v.q, v.c, v.D, v.j, got, v.want)
		}
	}
	for D := uint64(3); D <= 13; D++ {
		for c := uint64(1); c < D; c++ {
			q := D - 1
			if ReferenceOrbit(q, c, D, 1) == 0 {
				t.Fatalf("early return q=%d c=%d D=%d", q, c, D)
			}
			if ReferenceOrbit(q, c, D, 2) != 0 {
				t.Fatalf("no return at two q=%d c=%d D=%d", q, c, D)
			}
			if AccessOrbitU64(q, c, D, 2) != 0 || AccessOrbitU64(q, c, D, 1) == 0 {
				t.Fatalf("production slice q=%d c=%d D=%d", q, c, D)
			}
		}
	}
}

// TestSweepTotals pins the per-slice certificate counts and the total, so a
// silent change of bounds or of a sweep body fails the test.
func TestSweepTotals(t *testing.T) {
	formula := SweepFormula()
	if formula.Checks != 133308 || formula.Failures != 0 {
		t.Fatalf("formula slice: %d checks, %d failures", formula.Checks, formula.Failures)
	}
	criterion := SweepCriterion()
	if criterion.Checks != 126960 || criterion.Failures != 0 {
		t.Fatalf("criterion slice: %d checks, %d failures", criterion.Checks, criterion.Failures)
	}
	order := SweepOrder()
	if order.Checks != 103467 || order.Failures != 0 {
		t.Fatalf("order slice: %d checks, %d failures", order.Checks, order.Failures)
	}
	full := SweepFullAccess()
	if full.Checks != 1433 || full.Failures != 0 {
		t.Fatalf("full-access slice: %d checks, %d failures", full.Checks, full.Failures)
	}
	nonone := SweepPrimeNonOne()
	if nonone.Checks != 2044 || nonone.Failures != 0 {
		t.Fatalf("prime non-one slice: %d checks, %d failures", nonone.Checks, nonone.Failures)
	}
	examples := SweepExamples()
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
// arithmetic headroom they rely on: every product q*(D-1) + c in the sweeps
// stays below two to the fifty-eighth, the rectangle maximum being 564 and the
// prime maximum 492. The bound is a property of the printed ranges and is not
// enforced at run time.
func TestDocumentedRanges(t *testing.T) {
	if accessMaxQ != 24 || accessMaxC != 12 || accessMaxD != 24 || accessMaxJ != 20 {
		t.Fatal("rectangle bounds changed from the documented ones")
	}
	if accessPrimeQ != 40 {
		t.Fatal("prime multiplier bound changed from the documented one")
	}
	const guard = uint64(1) << 58
	if got := uint64(accessMaxQ*(accessMaxD-1) + accessMaxC); got != 564 {
		t.Fatalf("rectangle product %d differs from the documented 564", got)
	} else if got >= guard {
		t.Fatalf("rectangle product %d reaches the guard", got)
	}
	if got := uint64(accessPrimeQ*(13-1) + 12); got != 492 {
		t.Fatalf("prime product %d differs from the documented 492", got)
	} else if got >= guard {
		t.Fatalf("prime product %d reaches the guard", got)
	}
}

// TestWarmedOrbitAllocation checks that repeated walks reuse their storage:
// the residue step is a pure uint64 loop, and the order search reuses the
// buffers of its workspace so that after warm-up it allocates nothing. The
// order search uses modulus 2^40 + 1, where twice repeated forty times pairs
// to minus one, so the order of two is eighty and the multiplication reaches
// two machine words.
func TestWarmedOrbitAllocation(t *testing.T) {
	warm := ReferenceOrbit(23, 11, 24, 20)
	if warm >= 24 {
		t.Fatalf("reference orbit left the residue range: %d", warm)
	}
	if got := AccessOrbitU64(23, 11, 24, 20); got != warm {
		t.Fatalf("orbit %d differs from the reference %d", got, warm)
	}
	const wide = (uint64(1) << 40) + 1
	work := NewWorkspace()
	if m, found := LeastOrderBig(work, 2, wide, 400); !found || m != 80 {
		t.Fatalf("warm-up order: %d/%v want 80", m, found)
	}
	allocs := testing.AllocsPerRun(100, func() {
		if m, found := LeastOrderBig(work, 2, wide, 400); !found || m != 80 {
			t.Fatalf("order search: %d/%v want 80", m, found)
		}
	})
	if allocs != 0 {
		t.Fatalf("order search allocated %v values per run", allocs)
	}
}
