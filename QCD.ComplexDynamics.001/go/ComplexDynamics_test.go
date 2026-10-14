// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math"
	"math/big"
	"math/cmplx"
	"testing"
)

// ReferenceQuotient uses rational Gaussian elimination, independently of the adjugate code.
func ReferenceQuotient(m Model, d, z Point) (Point, bool) {
	a := new(big.Rat).SetInt64(d.Re)
	b := new(big.Rat).SetInt64(-m.Nu * d.Im)
	c := new(big.Rat).SetInt64(d.Im)
	e := new(big.Rat).SetInt64(d.Re + m.Tau*d.Im)
	x := new(big.Rat).SetInt64(z.Re)
	y := new(big.Rat).SetInt64(z.Im)
	if a.Sign() == 0 {
		a, c = c, a
		b, e = e, b
		x, y = y, x
	}
	if a.Sign() == 0 {
		panic("singular divisor matrix")
	}
	factor := new(big.Rat).Quo(c, a)
	e.Sub(e, new(big.Rat).Mul(factor, b))
	y.Sub(y, new(big.Rat).Mul(factor, x))
	v := new(big.Rat).Quo(y, e)
	u := new(big.Rat).Quo(new(big.Rat).Sub(x, new(big.Rat).Mul(b, v)), a)
	if !u.IsInt() || !v.IsInt() {
		return Point{}, false
	}
	return Point{u.Num().Int64(), v.Num().Int64()}, true
}

// TestDivision checks signed seeds, all small nonzero divisors and fence endpoints.
func TestDivision(t *testing.T) {
	for _, m := range []Model{{"Gaussian", 0, 1}, {"Eisenstein", -1, 1}} {
		for s := int64(-3); s <= 3; s++ {
			for v := int64(-3); v <= 3; v++ {
				d := Point{s, v}
				if d == (Point{}) {
					continue
				}
				for x := int64(-8); x <= 8; x++ {
					for y := int64(-8); y <= 8; y++ {
						z := Point{x, y}
						got, ok := Quotient(m, d, z)
						want, ref := ReferenceQuotient(m, d, z)
						if ok != ref || ok && got != want {
							t.Fatalf("%v divisor %v seed %v: %v/%v != %v/%v", m, d, z, got, ok, want, ref)
						}
						if ok && Multiply(m, d, got) != z {
							t.Fatal("failed exact reconstruction")
						}
					}
				}
				for _, z := range []Point{{CoordLimit, CoordLimit}, {-CoordLimit, CoordLimit},
					{CoordLimit, -CoordLimit}, {-CoordLimit, -CoordLimit}} {
					got, ok := Quotient(m, d, z)
					want, ref := ReferenceQuotient(m, d, z)
					if ok != ref || ok && got != want {
						t.Fatal("fence division mismatch")
					}
				}
			}
		}
	}
}

// TestOddEntry replays every step up to the proved 2*v2(y) bound, then twelve tail ticks.
func TestOddEntry(t *testing.T) {
	for _, m := range []Model{{"Gaussian", 0, 1}, {"Eisenstein", -1, 1}} {
		for _, c := range []int64{-1, 1} {
			f := Family{"off-axis", m, Point{3, 0}, Point{c, 0}, Point{2, 0}, "raw"}
			for r := 0; r <= 10; r++ {
				for x := int64(-16); x <= 16; x++ {
					for _, u := range []int64{-3, -1, 1, 3} {
						z := Point{x, (1 << r) * u}
						entry, divisions := 0, 0
						for z.Im%2 == 0 && entry <= 2*r {
							next, division := RawStep(f, z)
							if division {
								divisions++
							}
							z = next
							entry++
						}
						if entry > 2*r || divisions != r {
							t.Fatal("dyadic entry budget failed")
						}
						for j := 0; j < 12; j++ {
							next, division := RawStep(f, z)
							if division || next.Im != 3*z.Im {
								t.Fatal("odd tail failed")
							}
							z = next
						}
					}
				}
			}
		}
	}
}

// TestNoFieldOrResidueConflation checks a minimal non-descent and both ramified quotients.
func TestNoFieldOrResidueConflation(t *testing.T) {
	f := Families()[1]
	a, _ := RawStep(f, Point{})
	b, _ := RawStep(f, Point{2, 0})
	if a.Re%2 == b.Re%2 {
		t.Fatal("raw halving unexpectedly descends mod 2")
	}
	g, e := Model{"Gaussian", 0, 1}, Model{"Eisenstein", -1, 1}
	gn, en := Multiply(g, Point{1, 1}, Point{1, 1}), Multiply(e, Point{1, -1}, Point{1, -1})
	if Mod(gn.Re, 2) != 0 || Mod(gn.Im, 2) != 0 ||
		Mod(en.Re, 3) != 0 || Mod(en.Im, 3) != 0 {
		t.Fatal("ramified nilpotent control failed")
	}
	// In the inert quotients every nonzero element has an explicitly found inverse.
	for _, entry := range []struct {
		m Model
		p int
	}{{g, 3}, {e, 2}} {
		for x := 0; x < entry.p; x++ {
			for y := 0; y < entry.p; y++ {
				if x == 0 && y == 0 {
					continue
				}
				found := false
				for a := 0; a < entry.p; a++ {
					for b := 0; b < entry.p; b++ {
						z := Multiply(entry.m, Point{int64(x), int64(y)}, Point{int64(a), int64(b)})
						found = found || Mod(z.Re, entry.p) == 1 && Mod(z.Im, entry.p) == 0
					}
				}
				if !found {
					t.Fatal("inert quotient is not a field")
				}
			}
		}
	}
}

// TestFrobenius distinguishes the quadratic Galois fields from ramified nonfield controls.
func TestFrobenius(t *testing.T) {
	for _, entry := range []struct {
		m     Model
		p     int
		field bool
	}{{Model{"Gaussian", 0, 1}, 3, true}, {Model{"Eisenstein", -1, 1}, 2, true},
		{Model{"Gaussian", 0, 1}, 2, false}, {Model{"Eisenstein", -1, 1}, 3, false}} {
		m, p := entry.m, entry.p
		images, fixed, roots, inverses := FiniteArithmetic(m, p)
		if fixed != p {
			t.Fatal("Frobenius fixed elements are not the prime subfield")
		}
		if entry.field {
			if images != p*p || roots != 2 || inverses != p*p-1 {
				t.Fatal("quadratic field/Galois census failed")
			}
		} else if images != p || roots != p || inverses != p*p-p {
			t.Fatal("ramified nonfield census failed")
		}
		for y := 0; y < p; y++ {
			for x := 0; x < p; x++ {
				z := Point{int64(x), int64(y)}
				frob := FinitePower(m, z, p, p)
				if entry.field && FinitePower(m, frob, p, p) != z {
					t.Fatal("quadratic Frobenius does not have order two")
				}
				for b := 0; b < p; b++ {
					for a := 0; a < p; a++ {
						w := Point{int64(a), int64(b)}
						fw := FinitePower(m, w, p, p)
						sum := FinitePower(m, Point{z.Re + w.Re, z.Im + w.Im}, p, p)
						wantSum := Point{Mod(frob.Re+fw.Re, p), Mod(frob.Im+fw.Im, p)}
						prod := FinitePower(m, Multiply(m, z, w), p, p)
						want := Multiply(m, frob, fw)
						wantProd := Point{Mod(want.Re, p), Mod(want.Im, p)}
						if sum != wantSum || prod != wantProd {
							t.Fatal("Frobenius ring homomorphism law failed")
						}
					}
				}
			}
		}
	}
}

// TestCohomology compares component counts with exact incidence ranks in each coefficient field.
func TestCohomology(t *testing.T) {
	for _, m := range []Model{{"Gaussian", 0, 1}, {"Eisenstein", -1, 1}} {
		for _, p := range []int{2, 3} {
			s := FiniteAffine(m, p, "test")
			for _, rank := range s.Ranks {
				if rank != s.States-s.Components {
					t.Fatal("rank mismatch")
				}
			}
		}
	}
	// Exhaust all nonzero edge multipliers and all additive cochains on lengths 1,2,3.
	for _, p := range []int{2, 3, 5} {
		for n := 1; n <= 3; n++ {
			mulCount, addCount := 1, 1
			for j := 0; j < n; j++ {
				mulCount *= p - 1
				addCount *= p
			}
			lam, a := make([]int, n), make([]int, n)
			for lcode := 0; lcode < mulCount; lcode++ {
				code, holonomy := lcode, 1
				for j := range lam {
					lam[j] = 1 + code%(p-1)
					code /= p - 1
					holonomy = holonomy * lam[j] % p
				}
				wantDim := 0
				if holonomy == 1 {
					wantDim = 1
				}
				for acode := 0; acode < addCount; acode++ {
					code = acode
					for j := range a {
						a[j] = code % p
						code /= p
					}
					h, b, dim := TwistedCycle(lam, a, p)
					count := 0
					for u := 0; u < p; u++ {
						v := u
						for j, l := range lam {
							v = (l*v + a[j]) % p
						}
						if v == u {
							count++
						}
					}
					want := 1
					if h == 1 {
						want = 0
						if b == 0 {
							want = p
						}
					}
					if h != holonomy || count != want || dim != wantDim {
						t.Fatal("twisted reconstruction or dimension failed")
					}
				}
			}
		}
	}
}

// TestJuliaViews preserves the four models and resolves the previously invisible plus basin.
func TestJuliaViews(t *testing.T) {
	models, views := Polynomials(), PolynomialViews()
	if len(views) != 6 || len(models) != 4 {
		t.Fatal("unexpected model or view count")
	}
	for j, view := range views[4:] {
		model := models[j+2]
		if len(view.Coefficients) != len(model.Coefficients) {
			t.Fatal("zoom changed polynomial degree")
		}
		for k, coefficient := range view.Coefficients {
			if coefficient != model.Coefficients[k] {
				t.Fatal("zoom changed a polynomial coefficient")
			}
		}
		if view.MinX != .994 || view.MaxX != 1.006 || view.MinY != -.006 || view.MaxY != .006 {
			t.Fatal("zoom box does not match the declared budget")
		}
	}
	// This fixed-mesh visibility control is numerical, not a Julia-membership proof.
	counts := [2]int{}
	for j, view := range views[4:] {
		for _, level := range JuliaLevels(view) {
			if level > JuliaTicks {
				counts[j]++
			}
		}
	}
	if counts[0] != 0 || counts[1] == 0 {
		t.Fatalf("plus-cycle zoom is not informative: finite survivors=%v", counts)
	}
}

// TestPolynomials independently checks finite-node agreement and a radius-eight negative control.
func TestPolynomials(t *testing.T) {
	ps := Polynomials()
	for k, p := range ps {
		nodes := map[float64]float64{0: 0, 1: 2, 2: 1}
		if k >= 2 {
			nodes = map[float64]float64{0: 0, 1: 4, 4: 2, 2: 1}
		}
		for x, want := range nodes {
			if cmplx.Abs(Evaluate(p, complex(x, 0))-complex(want, 0)) > 1e-12 {
				t.Fatal("finite polynomial nodes mismatch")
			}
		}
		for angle := 0; angle < 256; angle++ {
			z := cmplx.Rect(8, 2*math.Pi*float64(angle)/256)
			if cmplx.Abs(Evaluate(p, z)) < 2*cmplx.Abs(z)-1e-10 {
				t.Fatal("escape bound control failed")
			}
		}
	}
	if cmplx.Abs(Evaluate(ps[0], 3)-8) < 1 {
		t.Fatal("finite interpolation wrongly called raw extension")
	}
}

// TestResidueVariants checks integral recovery and rejects applying the raw escape theorem.
func TestResidueVariants(t *testing.T) {
	for _, f := range Families()[9:] {
		for x := int64(-32); x <= 32; x++ {
			for y := int64(-32); y <= 32; y++ {
				z := Point{x, y}
				v, zero := RawStep(f, z)
				r := Point{Mod(x, 2), Mod(y, 2)}
				num := z
				if r != (Point{}) {
					q, a := Multiply(f.Ring, f.Q, z), Multiply(f.Ring, f.C, r)
					num = Point{q.Re + a.Re, q.Im + a.Im}
				}
				if Multiply(f.Ring, f.D, v) != num || zero != (r == (Point{})) {
					t.Fatalf("residue recovery failed for %s at %v", f.Name, z)
				}
				if ProvenOddTail(f, z) {
					t.Fatal("raw off-axis theorem applied to a different convention")
				}
			}
		}
		v, _ := RawStep(f, Point{1, 1})
		if f.C.Re == 1 {
			w, _ := RawStep(f, v)
			if v != (Point{2, 2}) || w != (Point{1, 1}) {
				t.Fatal("Joseph plus two-cycle lost")
			}
		} else if v != (Point{1, 1}) {
			t.Fatal("residue minus fixed point lost")
		}
	}
}

// ReferenceDependent tests positive powers through eight for coefficients at most sixty-four.
// For this bounded test, each prime exponent is at most six, so a dependent pair occurs here.
func ReferenceDependent(q, d int64) bool {
	var qp, dp, qb, db big.Int
	qb.SetInt64(q)
	db.SetInt64(d)
	qp.SetInt64(1)
	for a := 1; a <= 8; a++ {
		qp.Mul(&qp, &qb)
		dp.SetInt64(1)
		for b := 1; b <= 8; b++ {
			dp.Mul(&dp, &db)
			if qp.Cmp(&dp) == 0 {
				return true
			}
		}
	}
	return false
}

// TestScalarCertificates checks exact minors, bounded completeness, and excluded parameters.
func TestScalarCertificates(t *testing.T) {
	for q := int64(2); q <= 64; q++ {
		for d := int64(2); d <= 64; d++ {
			c, ok := IndependenceCertificate(q, d)
			if ok == ReferenceDependent(q, d) {
				t.Fatalf("independence mismatch: q=%d d=%d certificate=%+v", q, d, c)
			}
			if ok && (!big.NewInt(c.P).ProbablyPrime(20) ||
				!big.NewInt(c.R).ProbablyPrime(20) || c.QP*c.DR == c.QR*c.DP) {
				t.Fatal("invalid exponent-minor witness")
			}
			negative, signedOK := IndependenceCertificate(-q, -d)
			if signedOK != ok || signedOK && negative != c {
				t.Fatal("scalar signs changed the absolute-value certificate")
			}
		}
	}
	for _, pair := range [][2]int64{{0, 2}, {2, 0}, {1, 2}, {2, -1}, {65537, 2}} {
		if _, ok := IndependenceCertificate(pair[0], pair[1]); ok {
			t.Fatal("inadmissible or out-of-contract coefficient accepted")
		}
	}
	if _, ok := IndependenceCertificate(12, 18); !ok {
		t.Fatal("same prime support incorrectly treated as multiplicative dependence")
	}
}

// TestScalarTransverse checks signed legal ticks and the exact monomial invariant with big.Int.
func TestScalarTransverse(t *testing.T) {
	for _, q := range []int64{2, 3, 4, 12, -12} {
		for _, d := range []int64{2, 3, 8, 18, -3, -18} {
			for _, c := range []int64{-2, 0, 2} {
				f := Family{"scalar-test", Model{"Gaussian", 0, 1},
					Point{q, 0}, Point{c, 0}, Point{d, 0}, "raw"}
				for x := int64(-2); x <= 2; x++ {
					for y := int64(-2); y <= 2; y++ {
						z, a, b := Point{x, y}, int64(0), int64(0)
						seen := make(map[int64]bool, 17)
						for j := 0; j < 16 && Inside(z); j++ {
							left := new(big.Int).Exp(big.NewInt(d), big.NewInt(b), nil)
							left.Mul(left, big.NewInt(z.Im))
							right := new(big.Int).Exp(big.NewInt(q), big.NewInt(a), nil)
							right.Mul(right, big.NewInt(y))
							if left.Cmp(right) != 0 || a+b != int64(j) {
								t.Fatal("transverse product or raw clock lost")
							}
							magnitude := max(z.Im, -z.Im)
							if z.Im != 0 && ProvenScalarEscape(f, z) && seen[magnitude] {
								t.Fatal("independent scalar magnitudes repeated")
							}
							seen[magnitude] = true
							next, division := RawStep(f, z)
							ref, divisible := ReferenceQuotient(f.Ring, f.D, z)
							if !divisible {
								rx := new(big.Int).Mul(big.NewInt(q), big.NewInt(z.Re))
								rx.Add(rx, big.NewInt(c))
								ry := new(big.Int).Mul(big.NewInt(q), big.NewInt(z.Im))
								ref = Point{rx.Int64(), ry.Int64()}
							}
							if division != divisible || next != ref {
								t.Fatal("signed scalar tick disagrees with rational reference")
							}
							if division {
								b++
							} else {
								a++
							}
							z = next
						}
					}
				}
			}
		}
	}
}

// TestScalarControls rejects nonreal parameters and quotient clocks, and preserves the five-cycle.
func TestScalarControls(t *testing.T) {
	f := ScalarFamilies()[0]
	if !ProvenScalarEscape(f, Point{1, 2}) || ProvenScalarEscape(f, Point{1, 0}) {
		t.Fatal("even-offset theorem or real-axis boundary failed")
	}
	for _, field := range []string{"q", "c", "d", "convention"} {
		g := f
		switch field {
		case "q":
			g.Q.Im = 1
		case "c":
			g.C.Im = 1
		case "d":
			g.D.Im = 1
		case "convention":
			g.Convention = "residue"
		}
		if ProvenScalarEscape(g, Point{1, 2}) {
			t.Fatal("scalar theorem crossed its domain or clock boundary")
		}
	}
	g := ScalarFamilies()[5]
	z := Point{0, 1}
	for j, want := range []int64{1, 4, 16, 2, 8} {
		if z != (Point{0, want}) || ProvenScalarEscape(g, z) {
			t.Fatalf("dependent control at raw time %d", j)
		}
		z, _ = RawStep(g, z)
	}
	if z != (Point{0, 1}) {
		t.Fatal("nonreal five-cycle did not close")
	}
	if n := testing.AllocsPerRun(20, func() { ProvenScalarEscape(f, Point{3, 4}) }); n != 0 {
		t.Fatalf("scalar certificate allocations: %g", n)
	}
}

// TestWorkspaceReuse rejects per-seed heap allocations in the bounded lattice hot loop.
func TestWorkspaceReuse(t *testing.T) {
	w := Workspace{Seen: make(map[Point]int, Ticks+1)}
	f := Families()[4]
	Diagnose(f, Point{3, 4}, &w)
	allocs := testing.AllocsPerRun(20, func() { Diagnose(f, Point{3, 4}, &w) })
	if allocs != 0 {
		t.Fatalf("hot-loop allocations: %g", allocs)
	}
}
