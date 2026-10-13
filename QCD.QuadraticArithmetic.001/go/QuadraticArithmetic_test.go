// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math"
	"math/big"
	"math/bits"
	"testing"
)

// Cache retains independent integer-matrix arithmetic buffers across reference checks.
type Cache struct {
	x [14]big.Int
}

// ReferenceQuotient solves the multiplication matrix with arbitrary-precision integers.
func (c *Cache) ReferenceQuotient(m Model, d, z Point) (Point, bool) {
	x := c.x[:len(c.x)]
	x[0].SetInt64(d.Re)
	x[1].SetInt64(m.Nu)
	x[2].SetInt64(d.Im)
	x[1].Mul(&x[1], &x[2]).Neg(&x[1])
	x[3].SetInt64(m.Tau)
	x[3].Mul(&x[3], &x[2]).Add(&x[3], &x[0])
	x[5].Mul(&x[0], &x[3])
	x[6].Mul(&x[1], &x[2])
	x[5].Sub(&x[5], &x[6])
	if x[5].Sign() == 0 {
		panic("ReferenceQuotient: singular multiplication matrix")
	}
	x[9].SetInt64(z.Re)
	x[10].SetInt64(z.Im)
	x[7].Mul(&x[3], &x[9])
	x[11].Mul(&x[1], &x[10])
	x[7].Sub(&x[7], &x[11])
	x[8].Mul(&x[0], &x[10])
	x[11].Mul(&x[2], &x[9])
	x[8].Sub(&x[8], &x[11])
	x[12].QuoRem(&x[7], &x[5], &x[13])
	if x[13].Sign() != 0 {
		return Point{}, false
	}
	if !x[12].IsInt64() {
		panic("ReferenceQuotient: quotient exceeds int64")
	}
	u := x[12].Int64()
	x[12].QuoRem(&x[8], &x[5], &x[13])
	if x[13].Sign() != 0 {
		return Point{}, false
	}
	if !x[12].IsInt64() {
		panic("ReferenceQuotient: quotient exceeds int64")
	}
	return Point{u, x[12].Int64()}, true
}

// TestMatrixReference checks each bounded guard and quotient against independent exact arithmetic.
func TestMatrixReference(t *testing.T) {
	var cache Cache
	models := Models()
	for _, m := range models {
		for s := int64(-4); s <= 4; s++ {
			for v := int64(-4); v <= 4; v++ {
				if s == 0 && v == 0 {
					continue
				}
				d := Point{s, v}
				h, _, _ := MakeHermite(m, d)
				for x := int64(-8); x <= 8; x++ {
					for y := int64(-8); y <= 8; y++ {
						z := Point{x, y}
						want, div := cache.ReferenceQuotient(m, d, z)
						got, actual := ExactQuotient(m, d, z)
						if actual != div || actual && got != want {
							t.Fatalf("matrix mismatch: model=%v d=%v z=%v", m, d, z)
						}
						r := Reduce(h, z)
						if (r == (Point{})) != div {
							t.Fatalf("Hermite guard mismatch: model=%v d=%v z=%v", m, d, z)
						}
						_, member := cache.ReferenceQuotient(m, d, Point{z.Re - r.Re, z.Im - r.Im})
						if !member || r.Re < 0 || r.Re >= h.L || r.Im < 0 || r.Im >= h.G {
							t.Fatalf("invalid representative: model=%v d=%v z=%v r=%v", m, d, z, r)
						}
					}
				}
			}
		}
	}
}

// TestRawReference catches branch errors without sharing the production division predicate.
func TestRawReference(t *testing.T) {
	var cache Cache
	for _, m := range Models() {
		for x := int64(-8); x <= 8; x++ {
			for y := int64(-8); y <= 8; y++ {
				z, d, q, c := Point{x, y}, Point{1, 1}, Point{2, -1}, Point{-1, 2}
				want, div := cache.ReferenceQuotient(m, d, z)
				if !div {
					// These explicit coefficients are the independently expanded affine branch.
					want = Point{2*x + m.Nu*y - 1, -x + (2-m.Tau)*y + 2}
				}
				got, branch, ok := RawStep(m, q, c, d, z)
				if !ok || branch != div || got != want {
					t.Fatalf("raw mismatch: model=%v z=%v got=%v want=%v", m, z, got, want)
				}
			}
		}
	}
}

// TestQuotientNegativeControls rejects both always-dividing and never-dividing guards.
func TestQuotientNegativeControls(t *testing.T) {
	var cache Cache
	seenDivision, seenNondivision := false, false
	for n := int64(-8); n <= 8; n++ {
		_, div := cache.ReferenceQuotient(Model{Nu: 5}, Point{1, 1}, Point{n, 0})
		seenDivision = div || seenDivision
		seenNondivision = !div || seenNondivision
	}
	if !seenDivision || !seenNondivision {
		t.Fatal("reference does not reject both constant guard controls")
	}
	if !Witnesses() {
		t.Fatal("exact orbit witnesses failed")
	}
}

// TestFirstDivisionReference verifies all D samples using literal modular doubling.
func TestFirstDivisionReference(t *testing.T) {
	for d := int64(1); d <= NuMax; d++ {
		for n := int64(-256); n <= 256; n++ {
			want, reaches, state := 0, false, n
			// D+1 is at most 65, so seven doublings cover every finite first index.
			for j := 0; j <= 7; j++ {
				if state%(d+1) == 0 {
					want, reaches = j, true
					break
				}
				state *= 2
			}
			got, actual := FirstDivision(d, n)
			if actual != reaches || actual && got != want {
				t.Fatalf("first division mismatch: D=%d n=%d got=%d want=%d", d, n, got, want)
			}
		}
	}
}

// TestTwelveTickCycles checks primitive returns after stripping each exact division prefix.
func TestTwelveTickCycles(t *testing.T) {
	for _, d := range []int64{1, 3} {
		m, divisor := Model{Nu: d}, Point{1, 1}
		for x := int64(-4); x <= 4; x++ {
			for y := int64(-4); y <= 4; y++ {
				z := Point{x, y}
				if z == (Point{}) {
					continue
				}
				for {
					quotient, divides := ExactQuotient(m, divisor, z)
					if !divides {
						break
					}
					z = quotient
				}
				var states [13]Point
				var branches [12]bool
				if !Trace(m, Point{2, 0}, Point{}, divisor, z, states[:], branches[:]) {
					t.Fatal("cycle exceeded arithmetic contract")
				}
				if states[12] != z {
					t.Fatalf("missing twelve-tick return: D=%d seed=%v", d, z)
				}
				for i := 0; i < 12; i++ {
					for j := i + 1; j < 12; j++ {
						if states[i] == states[j] {
							t.Fatalf("nonprimitive cycle: D=%d seed=%v i=%d j=%d", d, z, i, j)
						}
					}
				}
			}
		}
	}
}

// TestOddOffsetTails checks the exact tail formula on dyadic moduli and both offset parities.
func TestOddOffsetTails(t *testing.T) {
	for _, d := range []int64{1, 3, 7, 15, 31, 63} {
		m, divisor := Model{Nu: d}, Point{1, 1}
		for cx := int64(-3); cx <= 3; cx++ {
			for cy := int64(-3); cy <= 3; cy++ {
				if (cx-cy)%2 == 0 {
					continue
				}
				c := Point{cx, cy}
				for x := int64(-4); x <= 4; x++ {
					for y := int64(-4); y <= 4; y++ {
						z := Point{x, y}
						if z == (Point{}) {
							continue
						}
						for {
							quotient, divides := ExactQuotient(m, divisor, z)
							if !divides {
								break
							}
							z = quotient
						}
						seed, factor := z, int64(1)
						for j := 0; j < 8; j++ {
							want := Point{factor*(seed.Re+c.Re) - c.Re,
								factor*(seed.Im+c.Im) - c.Im}
							if z != want {
								t.Fatalf("offset formula mismatch: D=%d c=%v seed=%v", d, c, seed)
							}
							next, div, ok := RawStep(m, Point{2, 0}, c, divisor, z)
							if !ok || div {
								t.Fatal("odd-offset tail does not remain affine")
							}
							z, factor = next, factor*2
						}
					}
				}
			}
		}
	}
}

// TestHenselReference checks every finite root rather than reusing the lifting recurrence.
func TestHenselReference(t *testing.T) {
	for e := 3; e <= 6; e++ {
		m := Model{Nu: int64(1<<e) - 1}
		for x := int64(-4); x <= 4; x++ {
			for y := int64(-4); y <= 4; y++ {
				seed := Point{x, y}
				if seed == (Point{}) {
					continue
				}
				v := bits.TrailingZeros64(uint64(x*x + m.Nu*y*y))
				precision := v + 1
				if precision < e+1 {
					precision = e + 1
				}
				modulus, roots := int64(1<<precision), 0
				hi, lo := HenselValuations(e, seed)
				for r := int64(0); r < modulus; r++ {
					if (r*r+m.Nu)%modulus != 0 ||
						bits.TrailingZeros64(uint64(1+r)) != e-1 {
						continue
					}
					// Norm precision makes both residues nonzero for every eligible root.
					a, b := (x+y*r)%modulus, (x-y*r)%modulus
					if a < 0 {
						a += modulus
					}
					if b < 0 {
						b += modulus
					}
					if a == 0 || b == 0 || bits.TrailingZeros64(uint64(a)) != hi ||
						bits.TrailingZeros64(uint64(b)) != lo {
						t.Fatalf("local valuation mismatch: e=%d seed=%v root=%d", e, seed, r)
					}
					roots++
				}
				if roots == 0 {
					t.Fatalf("reference found no oriented root: e=%d seed=%v", e, seed)
				}
			}
		}
	}
}

// TestDyadicWordReference compares all 128 guards with independent integer-matrix quotients.
func TestDyadicWordReference(t *testing.T) {
	var cache Cache
	for e := 3; e <= 6; e++ {
		m := Model{Nu: int64(1<<e) - 1}
		for x := int64(-4); x <= 4; x++ {
			for y := int64(-4); y <= 4; y++ {
				seed := Point{x, y}
				if seed == (Point{}) {
					continue
				}
				hi, lo := HenselValuations(e, seed)
				state := seed
				for j := 0; j < ValuationMax; j++ {
					quotient, divides := cache.ReferenceQuotient(m, Point{1, 1}, state)
					if DyadicGuard(e, hi, lo) != divides {
						t.Fatalf("word mismatch: e=%d seed=%v tick=%d", e, seed, j)
					}
					if divides {
						state, hi, lo = quotient, hi-(e-1), lo-1
					} else {
						// One division per e+1 ticks bounds reference coordinates below 2^61.
						state, hi, lo = Point{2 * state.Re, 2 * state.Im}, hi+1, lo+1
					}
				}
			}
		}
	}
}

// ExpectPanic keeps unsupported-input checks distinct from theorem counterexamples.
func ExpectPanic(t *testing.T, name string, f func()) {
	t.Helper()
	defer func() {
		if recover() == nil {
			t.Errorf("missing contract panic: %s", name)
		}
	}()
	f()
}

// TestUnsupportedInputs verifies that out-of-range inputs cannot silently produce certificates.
func TestUnsupportedInputs(t *testing.T) {
	ExpectPanic(t, "discriminant", func() { RequireModel(Model{Tau: 2, Nu: 1}) })
	ExpectPanic(t, "large Nu", func() { RequireModel(Model{Nu: NuMax + 1}) })
	ExpectPanic(t, "zero divisor", func() {
		ExactQuotient(Model{Nu: 1}, Point{}, Point{1, 0})
	})
	ExpectPanic(t, "minimal integer", func() { Bezout(math.MinInt64, 1) })
	ExpectPanic(t, "zero HNF diagonal", func() { Reduce(Hermite{G: 1}, Point{}) })
	ExpectPanic(t, "oversized HNF shear", func() {
		Reduce(Hermite{G: 1, L: 1, H: HermiteMax + 1}, Point{})
	})
	ExpectPanic(t, "D=0", func() { FirstDivision(0, 1) })
	ExpectPanic(t, "large D", func() { FirstDivision(NuMax+1, 1) })
	ExpectPanic(t, "unsupported label", func() { LabelText(`$x$`) })
	ExpectPanic(t, "nondyadic local exponent", func() { HenselValuations(2, Point{1, 0}) })
	ExpectPanic(t, "zero local seed", func() { HenselValuations(3, Point{}) })
	ExpectPanic(t, "unrealizable local pair", func() { DyadicGuard(3, 0, 1) })
}

// TestCertificateAndAllocations checks the exact predicate count and the hot arithmetic paths.
func TestCertificateAndAllocations(t *testing.T) {
	ok, count := RunCertificate()
	if !ok || count != 372704 {
		t.Fatalf("certificate failed: ok=%v count=%d", ok, count)
	}
	if a := testing.AllocsPerRun(10, func() { CheckModel(Model{Nu: 5}) }); a != 0 {
		t.Fatalf("certificate hot-loop allocations: %g", a)
	}
	if a := testing.AllocsPerRun(10, func() { CheckParameterDivision() }); a != 0 {
		t.Fatalf("parameter hot-loop allocations: %g", a)
	}
	if a := testing.AllocsPerRun(10, func() { CheckDyadicValuations() }); a != 0 {
		t.Fatalf("dyadic hot-loop allocations: %g", a)
	}
}
