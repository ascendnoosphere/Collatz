// SPDX-License-Identifier: CC-BY-4.0
// Exact lattice diagnostics, finite cochain checks, and noncanonical polynomial portraits.
package main

import (
	"encoding/json"
	"flag"
	"fmt"
	"image"
	"image/color"
	"log"
	"math"
	"math/cmplx"
	"os"
	"path/filepath"
	"runtime"
	"sort"
	"strings"
	"sync"

	"codeberg.org/go-fonts/latin-modern/lmmath"
	"codeberg.org/go-fonts/latin-modern/lmroman12regular"
	stdfnt "golang.org/x/image/font"
	"golang.org/x/image/font/sfnt"
	"golang.org/x/image/math/fixed"
	"gonum.org/v1/plot"
	"gonum.org/v1/plot/font"
	"gonum.org/v1/plot/text"
	"gonum.org/v1/plot/vg"
	"gonum.org/v1/plot/vg/draw"
	"gonum.org/v1/plot/vg/vgimg"
	"gonum.org/v1/plot/vg/vgpdf"
	"gonum.org/v1/plot/vg/vgsvg"
)

const (
	Radius              = 48
	Ticks               = 256
	Mesh                = 768
	JuliaTicks          = 256
	Workers             = 8
	CoordLimit    int64 = 1 << 26
	RawInputLimit int64 = 1 << 44
	CoeffLimit    int64 = 1 << 16
)

// Point stores the coefficients of 1,w; Im is not Im(z) in the Eisenstein basis.
type Point struct{ Re, Im int64 }

// Model fixes one imaginary quadratic order and its physical complex embedding.
type Model struct {
	Name    string
	Tau, Nu int64
}

// Family fixes a ring and a declared raw or residue-quotient convention.
type Family struct {
	Name       string
	Ring       Model
	Q, C, D    Point
	Convention string
}

// Result distinguishes proved tails from cutoff exits and undecided finite prefixes.
type Result struct {
	Class                    string
	Representative           Point
	Period, Steps, Divisions int
}

// Workspace reuses trajectory and hash buffers for an entire worker chunk.
type Workspace struct {
	Seen   map[Point]int
	States [Ticks + 1]Point
}

// Summary records the actual finite window and cochain-visible cycles for a family.
type Summary struct {
	Family        Family
	Radius, Ticks int
	Counts        map[string]int
	Cycles        []CycleSummary
}

// CycleSummary retains period and lattice mark, unlike unmarked H1 alone.
type CycleSummary struct {
	Representative Point
	Period, Seeds  int
}

// Polynomial fixes descending coefficients and the explicit complex-plane sampling box.
type Polynomial struct {
	Name                   string
	Coefficients           []float64
	MinX, MaxX, MinY, MaxY float64
}

// DynamicsReport separates exact finite lattice certificates from floating image diagnostics.
type DynamicsReport struct {
	Lattices                           []Summary
	ScalarLattices                     []Summary
	FiniteRings                        []FiniteSummary
	PolynomialViews                    []Polynomial
	PolynomialSurvivors                map[string]int
	PolynomialSamples, PolynomialTicks int
	TotalPolynomialSamples             int
	PolynomialEscapeRadius             float64
	Annotations                        bool
	PolynomialChecks                   map[string]HorizonCheck
}

// HorizonCheck compares two horizons on identical points, not exact Julia-set membership.
type HorizonCheck struct {
	Samples, EarlierSurvivors, LaterSurvivors, NewlyEscaped int
}

// Families supplies both classical signs and genuinely complex multipliers/divisors.
func Families() []Family {
	g, e := Model{"Gaussian", 0, 1}, Model{"Eisenstein", -1, 1}
	return []Family{
		{"GaussianPlus", g, Point{3, 0}, Point{1, 0}, Point{2, 0}, "raw"},
		{"GaussianMinus", g, Point{3, 0}, Point{-1, 0}, Point{2, 0}, "raw"},
		{"EisensteinPlus", e, Point{3, 0}, Point{1, 0}, Point{2, 0}, "raw"},
		{"EisensteinMinus", e, Point{3, 0}, Point{-1, 0}, Point{2, 0}, "raw"},
		{"GaussianRamified", g, Point{2, 0}, Point{1, 0}, Point{1, 1}, "raw"},
		{"GaussianRotated", g, Point{0, 2}, Point{1, 1}, Point{2, 0}, "raw"},
		{"EisensteinRotated", e, Point{0, 2}, Point{1, 0}, Point{2, 0}, "raw"},
		{"EisensteinRamified", e, Point{1, -1}, Point{1, 0}, Point{1, -1}, "raw"},
		{"GaussianSplit", g, Point{2, 1}, Point{}, Point{2, -1}, "raw"},
		{"GaussianJosephPlus", g, Point{3, 0}, Point{1, 0}, Point{2, 0}, "residue"},
		{"GaussianJosephMinus", g, Point{3, 0}, Point{-1, 0}, Point{2, 0}, "residue"},
		{"EisensteinResiduePlus", e, Point{3, 0}, Point{1, 0}, Point{2, 0}, "residue"},
		{"EisensteinResidueMinus", e, Point{3, 0}, Point{-1, 0}, Point{2, 0}, "residue"},
	}
}

// Norm is exact throughout the coordinate fence for the two supported orders.
func Norm(m Model, z Point) int64 {
	return z.Re*z.Re + m.Tau*z.Re*z.Im + m.Nu*z.Im*z.Im
}

// Inside prevents every subsequent small-parameter int64 operation from overflowing.
func Inside(z Point) bool {
	return -CoordLimit <= z.Re && z.Re <= CoordLimit &&
		-CoordLimit <= z.Im && z.Im <= CoordLimit
}

// Multiply uses the integral relation w*w=Tau*w-Nu, with fenced states and small parameters.
func Multiply(m Model, a, b Point) Point {
	return Point{a.Re*b.Re - m.Nu*a.Im*b.Im,
		a.Re*b.Im + a.Im*b.Re + m.Tau*a.Im*b.Im}
}

// Quotient checks both adjugate numerators, returning only an exact integral quotient.
func Quotient(m Model, d, z Point) (Point, bool) {
	n := Norm(m, d)
	if n <= 0 {
		panic("nonpositive divisor norm")
	}
	x := (d.Re+m.Tau*d.Im)*z.Re + m.Nu*d.Im*z.Im
	y := -d.Im*z.Re + d.Re*z.Im
	if x%n != 0 || y%n != 0 {
		return Point{}, false
	}
	return Point{x / n, y / n}, true
}

// SupportedFamily certifies the parameter bounds used by every int64 raw-tick operation.
func SupportedFamily(f Family) bool {
	if f.Ring.Nu != 1 || f.Ring.Tau != 0 && f.Ring.Tau != -1 || f.D == (Point{}) {
		return false
	}
	for _, z := range [3]Point{f.Q, f.C, f.D} {
		if z.Re < -CoeffLimit || z.Re > CoeffLimit ||
			z.Im < -CoeffLimit || z.Im > CoeffLimit {
			return false
		}
	}
	if f.Convention == "raw" {
		return true
	}
	return f.Convention == "residue" && f.Q == (Point{3, 0}) &&
		f.D == (Point{2, 0}) && (f.C == (Point{1, 0}) || f.C == (Point{-1, 0}))
}

// RawStep rejects unsupported inputs before arithmetic and never rounds a lattice quotient.
// With coordinates <= 2^44 and coefficients <= 2^16, every raw numerator is < 2^62+2^16.
func RawStep(f Family, z Point) (Point, bool) {
	if !SupportedFamily(f) || z.Re < -RawInputLimit || z.Re > RawInputLimit ||
		z.Im < -RawInputLimit || z.Im > RawInputLimit {
		panic("raw tick outside supported ring, parameter or coordinate bounds")
	}
	if f.Convention == "residue" {
		r := Point{Mod(z.Re, 2), Mod(z.Im, 2)}
		if r == (Point{}) {
			return Point{z.Re / 2, z.Im / 2}, true
		}
		v, a := Multiply(f.Ring, f.Q, z), Multiply(f.Ring, f.C, r)
		q, ok := Quotient(f.Ring, f.D, Point{v.Re + a.Re, v.Im + a.Im})
		if !ok {
			panic("inadmissible residue-quotient parameters")
		}
		return q, false
	}
	if f.Convention != "raw" {
		panic("unknown map convention")
	}
	if q, ok := Quotient(f.Ring, f.D, z); ok {
		return q, true
	}
	q := Multiply(f.Ring, f.Q, z)
	return Point{q.Re + f.C.Re, q.Im + f.C.Im}, false
}

// ExponentCertificate records two prime rows with a nonzero independence determinant.
type ExponentCertificate struct {
	P, R, QP, QR, DP, DR int64
}

// PrimeExponent counts an exact prime factor in a positive small coefficient.
func PrimeExponent(n, p int64) int64 {
	if n < 1 || p < 2 {
		panic("prime exponent requires n >= 1 and p >= 2")
	}
	e := int64(0)
	for n%p == 0 {
		n /= p
		e++
	}
	return e
}

// IndependenceCertificate factors bounded coefficients into a fixed, allocation-free buffer.
// The returned determinant is the sufficient criterion proved by ExponentIndependent in Lean.
func IndependenceCertificate(q, d int64) (ExponentCertificate, bool) {
	if q < -65536 || q > 65536 || d < -65536 || d > 65536 {
		return ExponentCertificate{}, false
	}
	q, d = max(q, -q), max(d, -d)
	if q < 2 || d < 2 {
		return ExponentCertificate{}, false
	}
	var primes [32]int64
	count := 0
	for _, coefficient := range [2]int64{q, d} {
		n := coefficient
		for p := int64(2); p <= n/p; p++ {
			if n%p != 0 {
				continue
			}
			primes[count], count = p, count+1
			for n%p == 0 {
				n /= p
			}
		}
		if n > 1 {
			primes[count], count = n, count+1
		}
	}
	// Duplicate prime rows are harmless; a nonzero minor supplies the complete witness.
	for i := 0; i < count; i++ {
		for j := i + 1; j < count; j++ {
			p, r := primes[i], primes[j]
			c := ExponentCertificate{p, r, PrimeExponent(q, p), PrimeExponent(q, r),
				PrimeExponent(d, p), PrimeExponent(d, r)}
			if c.QP*c.DR != c.QR*c.DP {
				return c, true
			}
		}
	}
	return ExponentCertificate{}, false
}

// ProvenScalarEscape applies transverse escape, or the all-seed homogeneous classification.
func ProvenScalarEscape(f Family, z Point) bool {
	if f.Convention != "raw" || f.Q.Im != 0 || f.C.Im != 0 || f.D.Im != 0 {
		return false
	}
	if z == (Point{}) || (z.Im == 0 && f.C != (Point{})) {
		return false
	}
	_, independent := IndependenceCertificate(f.Q.Re, f.D.Re)
	return independent
}

// ScalarFamilies tests even offsets, shared prime support, signed division and dependence.
func ScalarFamilies() []Family {
	g, e := Model{"Gaussian", 0, 1}, Model{"Eisenstein", -1, 1}
	return []Family{
		{"GaussianEvenOffset", g, Point{3, 0}, Point{2, 0}, Point{2, 0}, "raw"},
		{"GaussianCoprime", g, Point{2, 0}, Point{7, 0}, Point{3, 0}, "raw"},
		{"GaussianCommonSupport", g, Point{12, 0}, Point{}, Point{18, 0}, "raw"},
		{"EisensteinCommonSupport", e, Point{12, 0}, Point{5, 0}, Point{18, 0}, "raw"},
		{"GaussianSignedScalar", g, Point{-2, 0}, Point{-3, 0}, Point{-3, 0}, "raw"},
		{"GaussianDependentScalar", g, Point{4, 0}, Point{}, Point{8, 0}, "raw"},
	}
}

// ProvenOddTail invokes only the checked off-axis (3,c,2), odd real c theorem.
func ProvenOddTail(f Family, z Point) bool {
	return f.Convention == "raw" && f.Q == (Point{3, 0}) && f.D == (Point{2, 0}) &&
		f.C.Im == 0 && f.C.Re%2 != 0 && z.Im%2 != 0
}

// Earlier selects a rotation-independent marked cycle representative.
func Earlier(a, b Point) bool { return a.Re < b.Re || a.Re == b.Re && a.Im < b.Im }

// Diagnose records an exact cycle or theorem-backed escape; every other result remains finite.
func Diagnose(f Family, seed Point, w *Workspace) Result {
	clear(w.Seen)
	z, divisions := seed, 0
	for j := 0; j <= Ticks; j++ {
		if !Inside(z) {
			return Result{Class: "coordinate exit", Steps: j, Divisions: divisions}
		}
		if k, ok := w.Seen[z]; ok {
			rep := z
			for t := k; t < j; t++ {
				if Earlier(w.States[t], rep) {
					rep = w.States[t]
				}
			}
			return Result{"exact cycle", rep, j - k, j, divisions}
		}
		if ProvenScalarEscape(f, z) || ProvenOddTail(f, z) {
			class := "proved off-axis escape"
			if z.Im == 0 {
				class = "proved homogeneous escape"
			}
			return Result{Class: class, Steps: j, Divisions: divisions}
		}
		if j == Ticks {
			break
		}
		w.Seen[z], w.States[j] = j, z
		next, division := RawStep(f, z)
		if division {
			divisions++
		}
		z = next
	}
	return Result{Class: "unresolved prefix", Steps: Ticks, Divisions: divisions}
}

// ComputeLattice partitions independent seeds into fixed chunks, one workspace per worker.
func ComputeLattice(f Family) ([]Result, Summary) {
	side := 2*Radius + 1
	results := make([]Result, side*side)
	var wg sync.WaitGroup
	for k := 0; k < Workers; k++ {
		lo, hi := k*len(results)/Workers, (k+1)*len(results)/Workers
		wg.Add(1)
		go func(lo, hi int) {
			defer wg.Done()
			w := Workspace{Seen: make(map[Point]int, Ticks+1)}
			for j := lo; j < hi; j++ {
				seed := Point{int64(j%side - Radius), int64(j/side - Radius)}
				results[j] = Diagnose(f, seed, &w)
			}
		}(lo, hi)
	}
	wg.Wait()
	summary := Summary{Family: f, Radius: Radius, Ticks: Ticks, Counts: make(map[string]int)}
	cycles := make(map[Point]CycleSummary)
	for _, r := range results {
		summary.Counts[r.Class]++
		if r.Class == "exact cycle" {
			old := cycles[r.Representative]
			old.Representative, old.Period, old.Seeds = r.Representative, r.Period, old.Seeds+1
			cycles[r.Representative] = old
		}
	}
	for _, c := range cycles {
		summary.Cycles = append(summary.Cycles, c)
	}
	sort.Slice(summary.Cycles, func(i, j int) bool {
		return Earlier(summary.Cycles[i].Representative, summary.Cycles[j].Representative)
	})
	return results, summary
}

// Embed places an integral basis point in the actual complex plane.
func Embed(m Model, x, y float64) (float64, float64) {
	return x + float64(m.Tau)*y/2, math.Sqrt(float64(4*m.Nu-m.Tau*m.Tau)) * y / 2
}

// ClassColor gives three fixed status colors; finite cycle colors are stable marked hashes.
func ClassColor(r Result) color.Color {
	switch r.Class {
	case "proved off-axis escape", "proved homogeneous escape":
		return color.RGBA{R: 25, G: 50, B: 95, A: 255}
	case "coordinate exit":
		return color.RGBA{R: 225, G: 150, B: 45, A: 255}
	case "unresolved prefix":
		return color.RGBA{R: 140, G: 140, B: 140, A: 255}
	default:
		colors := [6]color.RGBA{{40, 150, 100, 255}, {200, 65, 90, 255}, {70, 155, 205, 255},
			{140, 70, 185, 255}, {175, 120, 55, 255}, {30, 175, 180, 255}}
		h := uint64(r.Representative.Re)*37 + uint64(r.Representative.Im)*101
		return colors[h%uint64(len(colors))]
	}
}

// LatticePanel fills disjoint embedded unit cells; it does not interpolate an orbit on C.
type LatticePanel struct {
	Ring    Model
	Results []Result
}

// Plot coalesces equally colored adjacent cells without interpolating any lattice state.
func (l LatticePanel) Plot(c draw.Canvas, p *plot.Plot) {
	trX, trY := p.Transforms(&c)
	side := 2*Radius + 1
	var path vg.Path
	for row := 0; row < side; row++ {
		for x := 0; x < side; {
			shade := ClassColor(l.Results[row*side+x])
			end := x + 1
			for end < side && ClassColor(l.Results[row*side+end]) == shade {
				end++
			}
			a, b := float64(x-Radius)-.5, float64(row-Radius)-.5
			width := float64(end - x)
			path = path[:0]
			for k, corner := range [4][2]float64{{0, 0}, {width, 0}, {width, 1}, {0, 1}} {
				u, v := Embed(l.Ring, a+corner[0], b+corner[1])
				pt := vg.Point{X: trX(u), Y: trY(v)}
				if k == 0 {
					path.Move(pt)
				} else {
					path.Line(pt)
				}
			}
			path.Close()
			c.SetColor(shade)
			c.Fill(path)
			x = end
		}
	}
}

// Polynomials are finite-orbit models, never alleged extensions on the entire lattice.
func Polynomials() []Polynomial {
	return []Polynomial{
		{"MinusQuadratic", []float64{-1.5, 3.5, 0}, -2, 4, -3, 3},
		{"MinusCritical", []float64{.5, -3, 4.5, 0}, -2, 5, -3.5, 3.5},
		{"PlusCubic", []float64{7.0 / 6, -7, 59.0 / 6, 0}, -2, 6, -4, 4},
		{"PlusCritical", []float64{2.0 / 9, -7.0 / 18, -35.0 / 9, 145.0 / 18, 0}, -2, 6, -4, 4},
	}
}

// PolynomialViews resolves the small plus-cycle basin without changing any polynomial.
func PolynomialViews() []Polynomial {
	views := Polynomials()
	for _, index := range []int{2, 3} {
		zoom := views[index]
		zoom.Name += "Zoom"
		zoom.MinX, zoom.MaxX, zoom.MinY, zoom.MaxY = .994, 1.006, -.006, .006
		views = append(views, zoom)
	}
	return views
}

// Evaluate uses Horner order so every floating portrait has a reproducible numerical rule.
func Evaluate(p Polynomial, z complex128) complex128 {
	v := complex(p.Coefficients[0], 0)
	for _, a := range p.Coefficients[1:] {
		v = v*z + complex(a, 0)
	}
	return v
}

// EscapeLevel evaluates one binary64 orbit at a specified finite horizon and radius eight.
func EscapeLevel(p Polynomial, z complex128, horizon int) int {
	for tick := 0; tick <= horizon; tick++ {
		if cmplx.Abs(z) > 8 {
			return tick
		}
		if tick < horizon {
			z = Evaluate(p, z)
		}
	}
	return horizon + 1
}

// JuliaLevels colors time to the radius; finite survival remains undecided.
func JuliaLevels(p Polynomial) []int {
	levels := make([]int, Mesh*Mesh)
	var wg sync.WaitGroup
	for k := 0; k < Workers; k++ {
		lo, hi := k*Mesh/Workers, (k+1)*Mesh/Workers
		wg.Add(1)
		go func(lo, hi int) {
			defer wg.Done()
			for y := lo; y < hi; y++ {
				im := p.MinY + (float64(y)+.5)*(p.MaxY-p.MinY)/Mesh
				for x := 0; x < Mesh; x++ {
					re := p.MinX + (float64(x)+.5)*(p.MaxX-p.MinX)/Mesh
					levels[y*Mesh+x] = EscapeLevel(p, complex(re, im), JuliaTicks)
				}
			}
		}(lo, hi)
	}
	wg.Wait()
	return levels
}

// JuliaColor uses contrasting bands; black means only finite-horizon survival.
func JuliaColor(level int) color.RGBA {
	if level > JuliaTicks {
		return color.RGBA{R: 18, G: 18, B: 24, A: 255}
	}
	t := float64(level) / 6
	return color.RGBA{R: uint8(125 + 110*math.Cos(t)), G: uint8(125 + 110*math.Cos(t+2)),
		B: uint8(125 + 110*math.Cos(t+4)), A: 255}
}

// JuliaPanel is a finite-time floating approximation, not a certificate of Julia membership.
type JuliaPanel struct {
	Polynomial Polynomial
	Levels     []int
	Raster     bool
}

// Plot uses a single raster tile for PNG and coalesced vector cells for SVG and PDF.
func (j JuliaPanel) Plot(c draw.Canvas, p *plot.Plot) {
	trX, trY := p.Transforms(&c)
	poly := j.Polynomial
	// A single image prevents independently antialiased cell edges from exposing white seams.
	if j.Raster {
		img := image.NewRGBA(image.Rect(0, 0, Mesh, Mesh))
		for y := 0; y < Mesh; y++ {
			for x := 0; x < Mesh; x++ {
				img.SetRGBA(x, Mesh-1-y, JuliaColor(j.Levels[y*Mesh+x]))
			}
		}
		c.DrawImage(vg.Rectangle{
			Min: vg.Point{X: trX(poly.MinX), Y: trY(poly.MinY)},
			Max: vg.Point{X: trX(poly.MaxX), Y: trY(poly.MaxY)},
		}, img)
		return
	}
	dx, dy := (poly.MaxX-poly.MinX)/Mesh, (poly.MaxY-poly.MinY)/Mesh
	var path vg.Path
	for y := 0; y < Mesh; y++ {
		for x := 0; x < Mesh; {
			level := j.Levels[y*Mesh+x]
			end := x + 1
			for end < Mesh && j.Levels[y*Mesh+end] == level {
				end++
			}
			a, b := poly.MinX+float64(x)*dx, poly.MinY+float64(y)*dy
			right := poly.MinX + float64(end)*dx
			path = path[:0]
			path.Move(vg.Point{X: trX(a), Y: trY(b)})
			path.Line(vg.Point{X: trX(right), Y: trY(b)})
			path.Line(vg.Point{X: trX(right), Y: trY(b + dy)})
			path.Line(vg.Point{X: trX(a), Y: trY(b + dy)})
			path.Close()
			c.SetColor(JuliaColor(level))
			c.Fill(path)
			x = end
		}
	}
}

// LegendEntry associates a figure meaning with its displayed swatch.
type LegendEntry struct {
	Label string
	Color color.Color
}

// LegendPanel draws an opaque key, preserving text contrast over every dynamical color.
type LegendPanel struct{ Entries []LegendEntry }

// Plot measures and draws the legend with the identical Latin Modern font handler.
func (l LegendPanel) Plot(c draw.Canvas, p *plot.Plot) {
	if len(l.Entries) == 0 {
		return
	}
	style := p.Legend.TextStyle
	style.Color = color.Black
	style.Font.Size = 12
	width := vg.Length(0)
	for _, entry := range l.Entries {
		w, _, _ := p.TextHandler.Box(entry.Label, style.Font)
		width = max(width, w)
	}
	left, top := c.Min.X+vg.Points(6), c.Max.Y-vg.Points(6)
	line := vg.Points(17)
	bottom := top - line*vg.Length(len(l.Entries)) - vg.Points(8)
	c.FillPolygon(color.White, []vg.Point{{X: left, Y: bottom},
		{X: left + width + vg.Points(34), Y: bottom},
		{X: left + width + vg.Points(34), Y: top}, {X: left, Y: top}})
	for j, entry := range l.Entries {
		y := top - vg.Points(17) - line*vg.Length(j)
		c.FillPolygon(entry.Color, []vg.Point{{X: left + vg.Points(6), Y: y},
			{X: left + vg.Points(17), Y: y}, {X: left + vg.Points(17), Y: y + vg.Points(10)},
			{X: left + vg.Points(6), Y: y + vg.Points(10)}})
		c.FillText(style, vg.Point{X: left + vg.Points(24), Y: y}, entry.Label)
	}
}

// AddLatticeLegend includes only the outcomes present in this exact finite seed window.
func AddLatticeLegend(p *plot.Plot, summary Summary) {
	entries := make([]LegendEntry, 0, 4)
	if summary.Counts["proved off-axis escape"]+summary.Counts["proved homogeneous escape"] > 0 {
		entries = append(entries, LegendEntry{"proved escape",
			ClassColor(Result{Class: "proved off-axis escape"})})
	}
	if summary.Counts["exact cycle"] > 0 {
		entries = append(entries, LegendEntry{"exact cycle (hashed colors)",
			ClassColor(Result{Class: "exact cycle"})})
	}
	for _, name := range []string{"coordinate exit", "unresolved prefix"} {
		if summary.Counts[name] > 0 {
			entries = append(entries, LegendEntry{name, ClassColor(Result{Class: name})})
		}
	}
	p.Add(LegendPanel{entries})
}

// CycleMark highlights an actual marked periodic seed, not an inferred basin boundary.
type CycleMark struct {
	Ring  Model
	Cycle CycleSummary
}

// Plot labels the period using a white backing and an explicitly sized four-point marker.
func (m CycleMark) Plot(c draw.Canvas, p *plot.Plot) {
	x, y := Embed(m.Ring, float64(m.Cycle.Representative.Re), float64(m.Cycle.Representative.Im))
	trX, trY := p.Transforms(&c)
	pt := vg.Point{X: trX(x), Y: trY(y)}
	style := p.Legend.TextStyle
	style.Font.Size, style.Color = 12, color.Black
	label := fmt.Sprintf("period %d", m.Cycle.Period)
	width, _, _ := p.TextHandler.Box(label, style.Font)
	left := min(pt.X+vg.Points(7), c.Max.X-width-vg.Points(6))
	base := min(pt.Y+vg.Points(7), c.Max.Y-vg.Points(18))
	c.FillPolygon(color.White, []vg.Point{{X: left - vg.Points(2), Y: base - vg.Points(2)},
		{X: left + width + vg.Points(2), Y: base - vg.Points(2)},
		{X: left + width + vg.Points(2), Y: base + vg.Points(14)},
		{X: left - vg.Points(2), Y: base + vg.Points(14)}})
	c.FillText(style, vg.Point{X: left, Y: base}, label)
	c.DrawGlyph(draw.GlyphStyle{Color: color.RGBA{240, 205, 40, 255},
		Radius: vg.Points(4), Shape: draw.RingGlyph{}}, pt)
}

// AddCycleMark chooses the closest nontrivial marked cycle so a label stays near the center.
func AddCycleMark(p *plot.Plot, summary Summary) {
	best := CycleSummary{}
	score := int64(1 << 62)
	for _, cycle := range summary.Cycles {
		if cycle.Period <= 1 {
			continue
		}
		r := cycle.Representative
		next := r.Re*r.Re + r.Im*r.Im
		if next < score {
			best, score = cycle, next
		}
	}
	if best.Period > 1 {
		p.Add(CycleMark{summary.Family.Ring, best})
	}
}

// EdgePairs joins midpoint crossings; alternating masks use a declared fixed pairing.
func EdgePairs(mask [4]bool) ([4]int, int) {
	var edges [4]int
	count := 0
	for j := 0; j < 4; j++ {
		if mask[j] != mask[(j+1)%4] {
			edges[count] = j
			count++
		}
	}
	return edges, count
}

// SampleEdge marks only an interpolated edge of the finite sampled survivor mask.
type SampleEdge struct{ Panel JuliaPanel }

// Plot traces midpoint segments, without identifying them with the infinite Julia boundary.
func (b SampleEdge) Plot(c draw.Canvas, p *plot.Plot) {
	trX, trY := p.Transforms(&c)
	poly, levels := b.Panel.Polynomial, b.Panel.Levels
	dx, dy := (poly.MaxX-poly.MinX)/Mesh, (poly.MaxY-poly.MinY)/Mesh
	c.SetColor(color.RGBA{245, 205, 45, 255})
	c.SetLineWidth(vg.Points(.6))
	var path vg.Path
	for y := 0; y < Mesh-1; y++ {
		for x := 0; x < Mesh-1; x++ {
			edges, count := EdgePairs([4]bool{levels[y*Mesh+x] > JuliaTicks,
				levels[y*Mesh+x+1] > JuliaTicks, levels[(y+1)*Mesh+x+1] > JuliaTicks,
				levels[(y+1)*Mesh+x] > JuliaTicks})
			if count == 0 {
				continue
			}
			a, d := poly.MinX+float64(x)*dx, poly.MinY+float64(y)*dy
			vertices := [4]vg.Point{{X: trX(a + dx), Y: trY(d + dy/2)},
				{X: trX(a + 1.5*dx), Y: trY(d + dy)},
				{X: trX(a + dx), Y: trY(d + 1.5*dy)},
				{X: trX(a + dx/2), Y: trY(d + dy)}}
			path = path[:0]
			for j := 0; j < count; j += 2 {
				path.Move(vertices[edges[j]])
				path.Line(vertices[edges[j+1]])
			}
			c.Stroke(path)
		}
	}
}

// CompareHorizons reuses a centered subgrid to measure finite-horizon losses at fixed points.
func CompareHorizons(poly Polynomial, levels []int) HorizonCheck {
	check := HorizonCheck{}
	for y := 1; y < Mesh; y += 3 {
		im := poly.MinY + (float64(y)+.5)*(poly.MaxY-poly.MinY)/Mesh
		for x := 1; x < Mesh; x += 3 {
			re := poly.MinX + (float64(x)+.5)*(poly.MaxX-poly.MinX)/Mesh
			early := EscapeLevel(poly, complex(re, im), 128)
			late := levels[y*Mesh+x]
			check.Samples++
			if early > 128 {
				check.EarlierSurvivors++
			}
			if late > JuliaTicks {
				check.LaterSurvivors++
			}
			if early > 128 && late <= JuliaTicks {
				check.NewlyEscaped++
			}
			if early <= 128 && early != late {
				panic("finite escape time changed on an identical sample")
			}
		}
	}
	return check
}

// FiniteSummary reports state-ring arithmetic separately from the cochain coefficient field.
type FiniteSummary struct {
	Name                                     string
	Modulus, States, Components              int
	FrobeniusImages, FrobeniusFixed          int
	DefiningRoots, InvertibleNonzeroElements int
	CycleLengths                             []int
	Ranks                                    map[int]int
}

// Mod returns the least nonnegative integer residue, including for negative coefficients.
func Mod(x int64, p int) int64 {
	r := x % int64(p)
	if r < 0 {
		r += int64(p)
	}
	return r
}

// FinitePower computes powers in one of the declared characteristic-two/three quotient rings.
func FinitePower(m Model, z Point, exponent, p int) Point {
	if exponent < 0 || (p != 2 && p != 3) {
		panic("finite quadratic power requires nonnegative exponent and characteristic 2 or 3")
	}
	z = Point{Mod(z.Re, p), Mod(z.Im, p)}
	result := Point{1, 0}
	for exponent > 0 {
		if exponent%2 == 1 {
			v := Multiply(m, result, z)
			result = Point{Mod(v.Re, p), Mod(v.Im, p)}
		}
		v := Multiply(m, z, z)
		z = Point{Mod(v.Re, p), Mod(v.Im, p)}
		exponent /= 2
	}
	return result
}

// FiniteArithmetic counts Frobenius images/fixed points, defining roots and actual inverses.
func FiniteArithmetic(m Model, p int) (images, fixed, roots, invertible int) {
	if p != 2 && p != 3 {
		panic("finite arithmetic requires characteristic 2 or 3")
	}
	var seen [9]bool
	for y := 0; y < p; y++ {
		for x := 0; x < p; x++ {
			z := Point{int64(x), int64(y)}
			v := FinitePower(m, z, p, p)
			seen[int(v.Re)+p*int(v.Im)] = true
			if v == z {
				fixed++
			}
			sq := Multiply(m, z, z)
			if Mod(sq.Re-m.Tau*z.Re+m.Nu, p) == 0 &&
				Mod(sq.Im-m.Tau*z.Im, p) == 0 {
				roots++
			}
			// Search all candidate inverses, including in the two nonfield controls.
			found := false
			for b := 0; b < p; b++ {
				for a := 0; a < p; a++ {
					product := Multiply(m, z, Point{int64(a), int64(b)})
					found = found || Mod(product.Re, p) == 1 && Mod(product.Im, p) == 0
				}
			}
			if found {
				invertible++
			}
		}
	}
	for _, present := range seen[:p*p] {
		if present {
			images++
		}
	}
	return images, fixed, roots, invertible
}

// MatrixRank reduces a rectangular matrix in place over characteristics 2, 3, or 5.
// Signed and large entries are normalized before products; ragged rows are rejected.
func MatrixRank(a [][]int, p int) int {
	if p != 2 && p != 3 && p != 5 {
		panic("cochain coefficient characteristic must be 2, 3, or 5")
	}
	if len(a) == 0 {
		return 0
	}
	columns := len(a[0])
	for _, row := range a {
		if len(row) != columns {
			panic("cochain matrix must be rectangular")
		}
		row = row[:len(row)]
		for j, entry := range row {
			row[j] = entry % p
			if row[j] < 0 {
				row[j] += p
			}
		}
	}
	rank := 0
	for col := 0; col < columns && rank < len(a); col++ {
		pivot := rank
		for pivot < len(a) && a[pivot][col]%p == 0 {
			pivot++
		}
		if pivot == len(a) {
			continue
		}
		a[rank], a[pivot] = a[pivot], a[rank]
		inv := 1
		for inv < p && a[rank][col]*inv%p != 1 {
			inv++
		}
		if inv == p {
			panic("noninvertible pivot in prime coefficient field")
		}
		for j := col; j < len(a[0]); j++ {
			a[rank][j] = a[rank][j] * inv % p
		}
		for i := 0; i < len(a); i++ {
			if i == rank {
				continue
			}
			factor := a[i][col]
			for j := col; j < len(a[0]); j++ {
				a[i][j] = (a[i][j] - factor*a[rank][j]) % p
				if a[i][j] < 0 {
					a[i][j] += p
				}
			}
		}
		rank++
	}
	return rank
}

// FiniteAffine studies z->w*z+1 on the whole finite quadratic ring, not raw halving.
func FiniteAffine(m Model, modulus int, name string) FiniteSummary {
	if modulus != 2 && modulus != 3 {
		panic("finite affine modulus must be 2 or 3")
	}
	n := modulus * modulus
	var edgeBuffer, generationBuffer, positionBuffer, pathBuffer [9]int
	var finishedBuffer [9]bool
	edges := edgeBuffer[:n]
	for i := range edges {
		z := Point{int64(i % modulus), int64(i / modulus)}
		t := Multiply(m, Point{0, 1}, z)
		edges[i] = int(Mod(t.Re+1, modulus)) + modulus*int(Mod(t.Im, modulus))
	}
	finished := finishedBuffer[:n]
	generation, position := generationBuffer[:n], positionBuffer[:n]
	path := pathBuffer[:0]
	summary := FiniteSummary{Name: name, Modulus: modulus, States: n, Ranks: make(map[int]int)}
	summary.FrobeniusImages, summary.FrobeniusFixed,
		summary.DefiningRoots, summary.InvertibleNonzeroElements = FiniteArithmetic(m, modulus)
	// A generation mark detects the current path without allocating a map per seed.
	for seed := 0; seed < n; seed++ {
		if finished[seed] {
			continue
		}
		path = path[:0]
		mark, z := seed+1, seed
		for !finished[z] {
			if generation[z] == mark {
				summary.CycleLengths = append(summary.CycleLengths, len(path)-position[z])
				break
			}
			generation[z], position[z] = mark, len(path)
			path = append(path, z)
			z = edges[z]
		}
		for _, state := range path {
			finished[state] = true
		}
	}
	sort.Ints(summary.CycleLengths)
	summary.Components = len(summary.CycleLengths)
	// The supported rings have at most nine states; reuse one bounded incidence matrix.
	var matrixBuffer [9][9]int
	var rowBuffer [9][]int
	a := rowBuffer[:n]
	for _, p := range []int{2, 3, 5} {
		for i := range a {
			clear(matrixBuffer[i][:])
			a[i] = matrixBuffer[i][:n]
			a[i][i] = (p - 1) % p
			a[i][edges[i]] = (a[i][edges[i]] + 1) % p
		}
		summary.Ranks[p] = MatrixRank(a, p)
		if summary.Ranks[p] != n-summary.Components {
			panic("graph cohomology rank mismatch")
		}
	}
	return summary
}

// TwistedCycle computes holonomy, translated holonomy and H1 dimension over a prime field.
func TwistedCycle(lam, a []int, p int) (int, int, int) {
	if len(lam) == 0 || len(lam) != len(a) || (p != 2 && p != 3 && p != 5) {
		panic("invalid twisted cycle")
	}
	h, b := 1, 0
	for j, l := range lam {
		if l <= 0 || l >= p {
			panic("local-system multiplier must be a nonzero field element")
		}
		h = h * l % p
		offset := int(Mod(int64(a[j]), p))
		b = (l*b + offset) % p
	}
	dim := 0
	if h == 1 {
		dim = 1
	}
	return h, b, dim
}

// WriteJSON publishes actual run data rather than inferred convergence claims.
func WriteJSON(path string, value any) {
	data, err := json.MarshalIndent(value, "", "  ")
	if err != nil {
		log.Fatal(err)
	}
	if err = os.WriteFile(path, append(data, '\n'), 0644); err != nil {
		log.Fatal(err)
	}
}

// FigureDirectory keeps generated data next to this content folder from any launch directory.
func FigureDirectory() string {
	_, file, _, ok := runtime.Caller(0)
	if !ok {
		panic("source location unavailable")
	}
	return filepath.Join(filepath.Dir(file), "..", "other")
}

// AddLatinModernFace parses an OpenType face into a local font collection.
func AddLatinModernFace(c *font.Collection, typeface string, data []byte) {
	face, err := sfnt.Parse(data)
	if err != nil {
		log.Fatal(err)
	}
	fnt := font.Font{Typeface: font.Typeface(typeface), Variant: "Serif"}
	*c = append(*c, font.Face{Font: fnt, Face: face})
}

// LatinModernCollection provides Roman ticks and full Unicode math glyphs.
func LatinModernCollection() font.Collection {
	var c font.Collection
	AddLatinModernFace(&c, "LatinModern", lmroman12regular.TTF)
	AddLatinModernFace(&c, "LatinModernMath", lmmath.TTF)
	return c
}

// MathLabels draws Latin Modern outlines; Gonum's TeX parser lacks these macros.
// Only the ten documented TeX expressions are supported. Other math fails loudly.
type MathLabels struct {
	text.Plain
}

// LabelText accepts exactly the ten mathematical labels used by these figures.
func LabelText(txt string) (string, bool) {
	if strings.ContainsAny(txt, "\r\n") {
		panic("multiline labels are not supported")
	}
	switch txt {
	case `$\operatorname{Re}z$`:
		return "Re 𝑧", true
	case `$\operatorname{Im}z$`:
		return "Im 𝑧", true
	case `$j$`:
		return "𝑗", true
	case `$B$`:
		return "𝐵", true
	case `$\log(1+N(z))$`:
		return "log(1+𝑁(𝑧))", true
	case `$3,6,1-\omega,2-2\omega,\ldots$`:
		return "3,6,1−𝜔,2−2𝜔,…", true
	case `$D$`:
		return "𝐷", true
	case `$1/\operatorname{odd}(D+1)$`:
		return "1/odd(𝐷+1)", true
	case `$\xi=D+n/2$`:
		return "𝜉=𝐷+𝑛/2", true
	case `$\eta=n/2+2h$`:
		return "𝜂=𝑛/2+2ℎ", true
	default:
		if strings.Contains(txt, "$") {
			panic("unsupported math label: " + txt)
		}
		return txt, false
	}
}

// LabelFont selects the math face only for TeX expressions.
func LabelFont(txt string, fnt font.Font) font.Font {
	_, mathLabel := LabelText(txt)
	if mathLabel {
		fnt.Typeface = "LatinModernMath"
	}
	return fnt
}

// Extents includes the supported math outlines and removes single-line leading.
// Latin Modern's nominal descent does not contain every mathematical italic glyph.
func (h MathLabels) Extents(fnt font.Font) font.Extents {
	ext := h.Plain.Extents(fnt)
	if fnt.Typeface == "LatinModernMath" {
		face := h.Fonts.Lookup(fnt, fnt.Size)
		ppem := fixed.Int26_6(math.Round(float64(fnt.Size) * 64))
		var buf sfnt.Buffer
		// This is the complete glyph repertoire of the ten supported expressions.
		for _, r := range "ReIm𝑧𝑗𝑁log(1+)36,−𝜔2…𝐷d/𝜉𝜂𝑛ℎ=𝐵" {
			glyph, err := face.Face.GlyphIndex(&buf, r)
			if err != nil || glyph == 0 {
				panic("missing Latin Modern glyph: " + string(r))
			}
			bounds, _, err := face.Face.GlyphBounds(&buf, glyph, ppem, stdfnt.HintingNone)
			if err != nil {
				panic(err)
			}
			ext.Ascent = max(ext.Ascent, -vg.Length(bounds.Min.Y)/64)
			ext.Descent = max(ext.Descent, vg.Length(bounds.Max.Y)/64)
		}
	}
	ext.Height = ext.Ascent + ext.Descent
	return ext
}

// Box uses the same complete outline extents and advance width as Draw.
func (h MathLabels) Box(txt string, fnt font.Font) (vg.Length, vg.Length, vg.Length) {
	label, _ := LabelText(txt)
	fnt = LabelFont(txt, fnt)
	face := h.Fonts.Lookup(fnt, fnt.Size)
	ext := h.Extents(fnt)
	return face.Width(label), ext.Ascent, ext.Descent
}

// GlyphPoint converts downward-positive font coordinates to canvas coordinates.
func GlyphPoint(p fixed.Point26_6, x vg.Length) vg.Point {
	return vg.Point{X: x + vg.Length(p.X)/64, Y: -vg.Length(p.Y) / 64}
}

// Draw renders scalable outlines, avoiding unsupported CFF embedding in the PDF backend.
func (h MathLabels) Draw(c vg.Canvas, txt string, sty text.Style, pt vg.Point) {
	label, _ := LabelText(txt)
	if label == "" {
		return
	}
	fnt := LabelFont(txt, sty.Font)
	face := h.Fonts.Lookup(fnt, fnt.Size)
	_, height, depth := h.Box(txt, sty.Font)
	ext := h.Extents(sty.Font)
	baseline := (height+depth)*vg.Length(sty.YAlign) + depth - (ext.Height - ext.Ascent)
	c.Push()
	defer c.Pop()
	c.Translate(pt)
	c.Rotate(sty.Rotation)
	c.SetColor(sty.Color)
	x := face.Width(label) * vg.Length(sty.XAlign)
	ppem := fixed.Int26_6(math.Round(float64(fnt.Size) * 64))
	var buf sfnt.Buffer
	var previous sfnt.GlyphIndex
	for i, r := range label {
		glyph, err := face.Face.GlyphIndex(&buf, r)
		if err != nil || glyph == 0 {
			panic("missing Latin Modern glyph: " + string(r))
		}
		if i > 0 {
			kern, err := face.Face.Kern(&buf, previous, glyph, ppem, stdfnt.HintingNone)
			if err != nil && err != sfnt.ErrNotFound {
				panic(err)
			}
			x += vg.Length(kern) / 64
		}
		segments, err := face.Face.LoadGlyph(&buf, glyph, ppem, nil)
		if err != nil {
			panic(err)
		}
		var path vg.Path
		for _, segment := range segments {
			// Place every outline control point relative to the aligned text baseline.
			point := func(i int) vg.Point {
				p := GlyphPoint(segment.Args[i], x)
				p.Y += baseline
				return p
			}
			switch segment.Op {
			case sfnt.SegmentOpMoveTo:
				if len(path) > 0 {
					path.Close()
				}
				path.Move(point(0))
			case sfnt.SegmentOpLineTo:
				path.Line(point(0))
			case sfnt.SegmentOpQuadTo:
				path.QuadTo(point(0), point(1))
			case sfnt.SegmentOpCubeTo:
				path.CubeTo(point(0), point(1), point(2))
			}
		}
		if len(path) > 0 {
			path.Close()
			c.Fill(path)
		}
		advance, err := face.Face.GlyphAdvance(&buf, glyph, ppem, stdfnt.HintingNone)
		if err != nil {
			panic(err)
		}
		x += vg.Length(advance) / 64
		previous = glyph
	}
}

// RegisterLatinModern assigns local fonts without changing global plot defaults.
func RegisterLatinModern(p *plot.Plot) {
	handler := MathLabels{Plain: text.Plain{Fonts: font.NewCache(LatinModernCollection())}}
	p.TextHandler = handler
	styles := []*text.Style{
		&p.Title.TextStyle, &p.X.Label.TextStyle, &p.Y.Label.TextStyle,
		&p.X.Tick.Label, &p.Y.Tick.Label, &p.Legend.TextStyle,
	}
	for i, style := range styles {
		style.Font.Typeface = "LatinModern"
		// Layout and drawing must agree on math metrics, including the title descent.
		if i < 3 {
			style.Font.Typeface = "LatinModernMath"
		}
		style.Font.Variant = "Serif"
		style.Handler = handler
	}
}

// NewPlot fixes the font, geometry-independent sizes, and explicit tick glyph sizes.
func NewPlot(title, xlabel, ylabel string) *plot.Plot {
	p := plot.New()
	RegisterLatinModern(p)
	p.Title.Text, p.X.Label.Text, p.Y.Label.Text = title, xlabel, ylabel
	p.Title.TextStyle.Font.Size = 16
	p.X.Label.TextStyle.Font.Size, p.Y.Label.TextStyle.Font.Size = 14, 14
	p.X.Tick.Label.Font.Size, p.Y.Tick.Label.Font.Size = 12, 12
	p.Legend.TextStyle.Font.Size = 12
	p.Legend.Top, p.Legend.Left = true, true
	p.Title.Padding, p.X.Label.Padding, p.Y.Label.Padding = vg.Points(4), vg.Points(4), vg.Points(4)
	return p
}

// SavePlot preserves scalable outlines in either a square or 3:2 vector PDF.
func SavePlot(p *plot.Plot, path string, square bool) {
	width, height := 6*vg.Inch, 4*vg.Inch
	if square {
		width, height = 5*vg.Inch, 5*vg.Inch
	}
	canvas := vgpdf.New(width, height)
	margin := vg.Points(4)
	p.Draw(draw.Crop(draw.New(canvas), margin, -margin, margin, -margin))
	f, err := os.Create(path)
	if err != nil {
		log.Fatal(err)
	}
	_, writeErr := canvas.WriteTo(f)
	closeErr := f.Close()
	if writeErr != nil {
		log.Fatal(writeErr)
	}
	if closeErr != nil {
		log.Fatal(closeErr)
	}
}

// SaveSVG publishes scalable outlines and cells without an embedded raster image.
func SaveSVG(p *plot.Plot, path string) {
	canvas := vgsvg.New(5*vg.Inch, 5*vg.Inch)
	margin := vg.Points(4)
	p.Draw(draw.Crop(draw.New(canvas), margin, -margin, margin, -margin))
	file, err := os.Create(path)
	if err != nil {
		log.Fatal(err)
	}
	_, err = canvas.WriteTo(file)
	closeErr := file.Close()
	if err != nil {
		log.Fatal(err)
	}
	if closeErr != nil {
		log.Fatal(closeErr)
	}
}

// SavePanel writes vector PDF/SVG and a 300-dpi, 1500-square preview from one plot.
func SavePanel(p *plot.Plot, base string, panels ...*JuliaPanel) {
	SavePlot(p, base+".pdf", true)
	SaveSVG(p, base+".svg")
	canvas := vgimg.NewWith(vgimg.UseWH(5*vg.Inch, 5*vg.Inch), vgimg.UseDPI(300))
	margin := vg.Points(4)
	// Plot records its drawing before replaying it, so the target type is not visible
	// inside a plotter. Select raster tiles explicitly for this preview pass.
	for _, panel := range panels {
		panel.Raster = true
	}
	p.Draw(draw.Crop(draw.New(canvas), margin, -margin, margin, -margin))
	for _, panel := range panels {
		panel.Raster = false
	}
	file, err := os.Create(base + ".png")
	if err != nil {
		log.Fatal(err)
	}
	_, err = (vgimg.PngCanvas{Canvas: canvas}).WriteTo(file)
	closeErr := file.Close()
	if err != nil {
		log.Fatal(err)
	}
	if closeErr != nil {
		log.Fatal(closeErr)
	}
}

// main declares and executes a bounded survey, keeping numerical and exact layers separate.
func main() {
	annotations := flag.Bool("annotations", true, "mark cycles and finite-horizon sampled edges")
	flag.Parse()
	dir := FigureDirectory()
	if err := os.MkdirAll(dir, 0755); err != nil {
		log.Fatal(err)
	}
	report := DynamicsReport{PolynomialViews: PolynomialViews(), PolynomialSamples: Mesh * Mesh,
		PolynomialTicks: JuliaTicks, PolynomialEscapeRadius: 8, Annotations: *annotations,
		PolynomialChecks: make(map[string]HorizonCheck)}
	report.TotalPolynomialSamples = len(report.PolynomialViews) * Mesh * Mesh
	report.PolynomialSurvivors = make(map[string]int, len(report.PolynomialViews))
	for _, f := range Families() {
		results, summary := ComputeLattice(f)
		report.Lattices = append(report.Lattices, summary)
		p := NewPlot(f.Name, "$\\operatorname{Re}z$", "$\\operatorname{Im}z$")
		p.Add(LatticePanel{f.Ring, results})
		AddLatticeLegend(p, summary)
		if *annotations {
			AddCycleMark(p, summary)
		}
		span := float64(Radius) + 1
		if f.Ring.Tau != 0 {
			span *= 1.5
		}
		p.X.Min, p.X.Max, p.Y.Min, p.Y.Max = -span, span, -span, span
		SavePanel(p, filepath.Join(dir, f.Name))
		fmt.Printf("%s: %v; %d exact marked cycles\n", f.Name, summary.Counts, len(summary.Cycles))
	}
	// Keep the thirteen-family historical census separate from the new scalar extension.
	for _, f := range ScalarFamilies() {
		results, summary := ComputeLattice(f)
		report.ScalarLattices = append(report.ScalarLattices, summary)
		p := NewPlot(f.Name, "$\\operatorname{Re}z$", "$\\operatorname{Im}z$")
		p.Add(LatticePanel{f.Ring, results})
		AddLatticeLegend(p, summary)
		if *annotations {
			AddCycleMark(p, summary)
		}
		span := float64(Radius) + 1
		if f.Ring.Tau != 0 {
			span *= 1.5
		}
		p.X.Min, p.X.Max, p.Y.Min, p.Y.Max = -span, span, -span, span
		SavePanel(p, filepath.Join(dir, f.Name))
		fmt.Printf("%s: %v; %d exact marked cycles\n", f.Name, summary.Counts, len(summary.Cycles))
	}
	for _, pmodel := range report.PolynomialViews {
		levels := JuliaLevels(pmodel)
		report.PolynomialSurvivors[pmodel.Name] = 0
		for _, level := range levels {
			if level > JuliaTicks {
				report.PolynomialSurvivors[pmodel.Name]++
			}
		}
		fmt.Printf("%s: %d/%d finite-horizon survivors\n", pmodel.Name,
			report.PolynomialSurvivors[pmodel.Name], len(levels))
		p := NewPlot(pmodel.Name, "$\\operatorname{Re}z$", "$\\operatorname{Im}z$")
		panel := JuliaPanel{Polynomial: pmodel, Levels: levels}
		p.Add(&panel)
		entries := []LegendEntry{{"survives 256 ticks", JuliaColor(JuliaTicks + 1)},
			{"escape-time bands", JuliaColor(12)}}
		if *annotations {
			p.Add(SampleEdge{panel})
			entries = append(entries, LegendEntry{"sampled edge (not Julia set)",
				color.RGBA{245, 205, 45, 255}})
		}
		p.Add(LegendPanel{entries})
		report.PolynomialChecks[pmodel.Name] = CompareHorizons(pmodel, levels)
		fmt.Printf("%s horizon check: %+v\n", pmodel.Name, report.PolynomialChecks[pmodel.Name])
		p.X.Min, p.X.Max, p.Y.Min, p.Y.Max = pmodel.MinX, pmodel.MaxX, pmodel.MinY, pmodel.MaxY
		// Close real coordinates need explicit decimal labels to avoid duplicate rounded ticks.
		if strings.HasSuffix(pmodel.Name, "Zoom") {
			p.X.Tick.Marker = plot.ConstantTicks{
				{Value: .995, Label: "0.995"}, {Value: 1, Label: "1"},
				{Value: 1.005, Label: "1.005"},
			}
			p.Y.Tick.Marker = plot.ConstantTicks{
				{Value: -.005, Label: "-0.005"}, {Value: 0, Label: "0"},
				{Value: .005, Label: "0.005"},
			}
		}
		SavePanel(p, filepath.Join(dir, pmodel.Name), &panel)
	}
	g, e := Model{"Gaussian", 0, 1}, Model{"Eisenstein", -1, 1}
	report.FiniteRings = []FiniteSummary{
		FiniteAffine(g, 2, "Gaussian mod 2: ramified, not a field"),
		FiniteAffine(g, 3, "Gaussian mod 3: GF(9)"),
		FiniteAffine(e, 2, "Eisenstein mod 2: GF(4)"),
		FiniteAffine(e, 3, "Eisenstein mod 3: ramified, not a field"),
	}
	WriteJSON(filepath.Join(dir, "DynamicsData.json"), report)
	figures := len(report.Lattices) + len(report.ScalarLattices) + len(report.PolynomialViews)
	fmt.Printf("%d vector PDFs, SVGs and PNG previews; data in DynamicsData.json\n", figures)
}
