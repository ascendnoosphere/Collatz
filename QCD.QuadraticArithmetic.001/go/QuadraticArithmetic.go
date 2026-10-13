// SPDX-License-Identifier: CC-BY-4.0
// Exact bounded quadratic-order arithmetic and discriminating orbit figures.
package main

import (
	"fmt"
	"image/color"
	"log"
	"math"
	"os"
	"path/filepath"
	"runtime"
	"strings"
	"sync"

	"codeberg.org/go-fonts/latin-modern/lmmath"
	"codeberg.org/go-fonts/latin-modern/lmroman12regular"
	stdfnt "golang.org/x/image/font"
	"golang.org/x/image/font/sfnt"
	"golang.org/x/image/math/fixed"
	"gonum.org/v1/plot"
	"gonum.org/v1/plot/font"
	"gonum.org/v1/plot/plotter"
	"gonum.org/v1/plot/text"
	"gonum.org/v1/plot/vg"
	"gonum.org/v1/plot/vg/draw"
	"gonum.org/v1/plot/vg/vgimg"
	"gonum.org/v1/plot/vg/vgpdf"
)

const (
	PointMax     int64 = 1000000
	ParamMax     int64 = 4
	GridMax      int64 = 6
	TraceMax           = 12
	NuMax        int64 = 64
	HermiteMax         = (NuMax + 2) * ParamMax * ParamMax
	ValuationMax       = 128
)

// Point records coefficients in the integral basis 1,w, not Cartesian coordinates.
type Point struct{ Re, Im int64 }

// Model specifies w^2-Tau*w+Nu=0 within the certified parameter range.
type Model struct {
	Name    string
	Tau, Nu int64
}

// Hermite stores the ideal basis (L,0),(H,G), with L,G positive.
type Hermite struct{ L, H, G int64 }

// Workspace reuses the finite instruction buffer across dyadic seed certificates.
type Workspace struct {
	Words [ValuationMax]bool
}

// Models fixes the five orders used by the certificate and figures.
func Models() [5]Model {
	return [5]Model{
		{"Gaussian", 0, 1}, {"Eisenstein", -1, 1},
		{"QuadraticTwo", 0, 2}, {"QuadraticThree", 0, 3}, {"QuadraticFive", 0, 5},
	}
}

// RequireModel excludes unsupported coefficients and degenerate discriminants.
func RequireModel(m Model) {
	if m.Tau < -1 || m.Tau > 1 || m.Nu < 1 || m.Nu > NuMax {
		panic("RequireModel: coefficients outside the certified range")
	}
}

// RequirePoint bounds every operand before int64 multiplication.
func RequirePoint(z Point, limit int64) {
	if z.Re < -limit || z.Re > limit || z.Im < -limit || z.Im > limit {
		panic("RequirePoint: coefficient outside the certified range")
	}
}

// Multiply is exact for bounded operands; each output coefficient is below 2^46.
func Multiply(m Model, z, w Point) Point {
	RequireModel(m)
	RequirePoint(z, PointMax)
	RequirePoint(w, PointMax)
	return Point{
		z.Re*w.Re - m.Nu*z.Im*w.Im,
		z.Re*w.Im + z.Im*w.Re + m.Tau*z.Im*w.Im,
	}
}

// Norm is the integral positive form; its value is below 2^46 on checked points.
func Norm(m Model, z Point) int64 {
	RequireModel(m)
	RequirePoint(z, PointMax)
	return z.Re*z.Re + m.Tau*z.Re*z.Im + m.Nu*z.Im*z.Im
}

// ExactQuotient tests both adjugate coordinates before any integer division.
func ExactQuotient(m Model, d, z Point) (Point, bool) {
	RequirePoint(d, ParamMax)
	RequirePoint(z, PointMax)
	n := Norm(m, d)
	if n == 0 {
		panic("ExactQuotient: zero divisor parameter")
	}
	a := (d.Re+m.Tau*d.Im)*z.Re + m.Nu*d.Im*z.Im
	b := -d.Im*z.Re + d.Re*z.Im
	if a%n != 0 || b%n != 0 {
		return Point{}, false
	}
	return Point{a / n, b / n}, true
}

// RawStep distinguishes arithmetic branch choice from an exceeded state bound.
func RawStep(m Model, q, c, d, z Point) (Point, bool, bool) {
	RequirePoint(q, ParamMax)
	RequirePoint(c, ParamMax)
	next, division := ExactQuotient(m, d, z)
	if !division {
		next = Multiply(m, q, z)
		next.Re += c.Re
		next.Im += c.Im
	}
	inRange := next.Re >= -PointMax && next.Re <= PointMax &&
		next.Im >= -PointMax && next.Im <= PointMax
	return next, division, inRange
}

// Bezout produces a positive gcd and signed coefficients for bounded inputs.
func Bezout(s, t int64) (int64, int64, int64) {
	RequirePoint(Point{s, t}, ParamMax)
	a, b := s, t
	if a < 0 {
		a = -a
	}
	if b < 0 {
		b = -b
	}
	oldr, r, oldu, u, oldv, v := a, b, int64(1), int64(0), int64(0), int64(1)
	for r != 0 {
		k := oldr / r
		oldr, r = r, oldr-k*r
		oldu, u = u, oldu-k*u
		oldv, v = v, oldv-k*v
	}
	if s < 0 {
		oldu = -oldu
	}
	if t < 0 {
		oldv = -oldv
	}
	return oldr, oldu, oldv
}

// MakeHermite keeps the skew term; a rectangular component reduction is unsound.
func MakeHermite(m Model, d Point) (Hermite, int64, int64) {
	RequirePoint(d, ParamMax)
	g, u, v := Bezout(d.Re, d.Im)
	if g == 0 {
		panic("MakeHermite: zero divisor parameter")
	}
	return Hermite{Norm(m, d) / g, d.Re*v - (m.Tau*d.Re+m.Nu*d.Im)*u, g}, u, v
}

// Mod returns the canonical residue for a positive modulus.
func Mod(n, m int64) int64 {
	if m <= 0 {
		panic("Mod: positive modulus required")
	}
	r := n % m
	if r < 0 {
		r += m
	}
	return r
}

// Reduce subtracts the vertical skew before reducing the horizontal coefficient.
func Reduce(h Hermite, z Point) Point {
	if h.G < 1 || h.G > ParamMax || h.L < 1 || h.L > HermiteMax ||
		h.H < -HermiteMax || h.H > HermiteMax {
		panic("Reduce: Hermite coefficients outside the certified range")
	}
	RequirePoint(z, PointMax)
	y := Mod(z.Im, h.G)
	k := (z.Im - y) / h.G
	return Point{Mod(z.Re-k*h.H, h.L), y}
}

// CheckModel checks all small guards, norm products, and canonical ideal invariance.
func CheckModel(m Model) (bool, int) {
	ok, count := true, 0
	for s := -ParamMax; s <= ParamMax; s++ {
		for t := -ParamMax; t <= ParamMax; t++ {
			d := Point{s, t}
			if d == (Point{}) {
				continue
			}
			h, u, v := MakeHermite(m, d)
			_, a := ExactQuotient(m, d, Point{h.L, 0})
			_, b := ExactQuotient(m, d, Point{h.H, h.G})
			det := ((s+m.Tau*t)/h.G)*u + (t/h.G)*(v-m.Tau*u)
			ok = a && ok
			ok = b && ok
			ok = (det == 1) && ok
			count += 3
			for x := -GridMax; x <= GridMax; x++ {
				for y := -GridMax; y <= GridMax; y++ {
					z := Point{x, y}
					r := Reduce(h, z)
					_, div := ExactQuotient(m, d, z)
					dz := Multiply(m, d, z)
					rx := Reduce(h, Point{x + s, y + t})
					ry := Reduce(h, Point{x - m.Nu*t, y + s + m.Tau*t})
					// Every predicate is evaluated even if an earlier case has failed.
					ok = (Norm(m, dz) == Norm(m, d)*Norm(m, z)) && ok
					ok = (div == (r == (Point{}))) && ok
					ok = (rx == r) && ok
					ok = (ry == r) && ok
					ok = (Reduce(h, r) == r) && ok
					count += 5
				}
			}
		}
	}
	return ok, count
}

// RunCertificate assigns disjoint model chunks to two workers and joins all results.
func RunCertificate() (bool, int) {
	models := Models()
	var flags [5]bool
	var counts [5]int
	var wg sync.WaitGroup
	for start := 0; start < len(models); start += 3 {
		end := start + 3
		if end > len(models) {
			end = len(models)
		}
		wg.Add(1)
		go func(lo, hi int) {
			defer wg.Done()
			for i := lo; i < hi; i++ {
				flags[i], counts[i] = CheckModel(models[i])
			}
		}(start, end)
	}
	wg.Wait()
	ok, count := true, 0
	for i := range flags {
		ok = flags[i] && ok
		count += counts[i]
	}
	parameterOK, parameterCount := CheckParameterDivision()
	ok = parameterOK && ok
	count += parameterCount
	dyadicOK, dyadicCount := CheckDyadicValuations()
	ok = dyadicOK && ok
	count += dyadicCount
	return ok, count
}

// TwoValuation extracts the first nonzero binary digit of a positive bounded integer.
func TwoValuation(n int64) int {
	if n < 1 || n >= 1<<46 {
		panic("TwoValuation: positive bounded input required")
	}
	v := 0
	for n%2 == 0 {
		n /= 2
		v++
	}
	return v
}

// HenselValuations computes both local valuations at precision fixed by the seed norm.
func HenselValuations(e int, z Point) (int, int) {
	if e < 3 || e > 6 || z == (Point{}) {
		panic("HenselValuations: unsupported exponent or zero seed")
	}
	RequirePoint(z, GridMax)
	m := Model{Nu: int64(1<<e) - 1}
	v := TwoValuation(Norm(m, z))
	precision := v + 1
	if precision < e+1 {
		precision = e + 1
	}
	modulus, u := int64(1<<precision), int64(1)
	// Precision is at most twelve; the largest pre-reduction product is below 2^28.
	for j := 0; j < precision; j++ {
		u = (1 + int64(1<<(e-2))*u*u) % modulus
	}
	r := Mod(-1+int64(1<<(e-1))*u, modulus)
	hi := TwoValuation(Mod(z.Re+z.Im*r, modulus))
	lo := TwoValuation(Mod(z.Re-z.Im*r, modulus))
	if hi+lo != v {
		panic("HenselValuations: norm factorization failed")
	}
	return hi, lo
}

// DyadicGuard retains the parity coupling of the order instead of dividing in a field.
func DyadicGuard(e, hi, lo int) bool {
	if e < 3 || e > 6 || hi < 0 || lo < 0 ||
		hi > ValuationMax+12 || lo > ValuationMax+12 || (hi == 0) != (lo == 0) {
		panic("DyadicGuard: unsupported or unrealizable valuation pair")
	}
	return hi == e-1 && lo == 1 || hi >= e && lo >= 2
}

// CheckSeedWord compares the exact valuation word with bounded raw steps and its proved tail.
func (w *Workspace) CheckSeedWord(e int, seed Point) bool {
	m := Model{Nu: int64(1<<e) - 1}
	hi, lo := HenselValuations(e, seed)
	v := hi + lo
	deadline, divisions, state := 5*v+7*e+1, 0, seed
	words := w.Words[:len(w.Words)]
	ok := true
	for j := range words {
		division := DyadicGuard(e, hi, lo)
		words[j] = division
		if j < TraceMax {
			// Only the twelve actual coordinate steps are subject to the state-size contract.
			next, actual, valid := RawStep(m, Point{2, 0}, Point{}, Point{1, 1}, state)
			ok = valid && actual == division && ok
			state = next
		}
		if division {
			hi, lo = hi-(e-1), lo-1
			divisions++
		} else {
			hi, lo = hi+1, lo+1
		}
		ok = (hi >= 0 && lo >= 0 && e*divisions <= j+1+v) && ok
		if seed == (Point{1, 0}) {
			ok = (divisions == j/e) && ok
		}
		if j >= deadline+e {
			ok = (words[j] == words[j-e]) && ok
			block := 0
			for k := 0; k < e; k++ {
				if words[j-k] {
					block++
				}
			}
			ok = (block == 1) && ok
		}
	}
	return ok
}

// CheckDyadicValuations covers every nonzero small seed without allocating in its loops.
func CheckDyadicValuations() (bool, int) {
	var workspace Workspace
	ok, count := true, 0
	for e := 3; e <= 6; e++ {
		for x := -GridMax; x <= GridMax; x++ {
			for y := -GridMax; y <= GridMax; y++ {
				seed := Point{x, y}
				if seed == (Point{}) {
					continue
				}
				ok = workspace.CheckSeedWord(e, seed) && ok
				count++
			}
		}
	}
	return ok, count
}

// Trace writes a bounded raw word; false signals an exceeded arithmetic contract.
func Trace(m Model, q, c, d, seed Point, states []Point, branches []bool) bool {
	if len(states) < 1 || len(states) > TraceMax+1 ||
		len(branches) != len(states)-1 {
		panic("Trace: unsupported buffer lengths")
	}
	states = states[:len(states)]
	branches = branches[:len(branches)]
	RequirePoint(seed, PointMax)
	states[0] = seed
	for j := 0; j < len(branches); j++ {
		next, div, ok := RawStep(m, q, c, d, states[j])
		if !ok {
			return false
		}
		states[j+1], branches[j] = next, div
	}
	return true
}

// Witnesses checks the two unit-phase cycles and the nonprincipal-order guard failure.
func Witnesses() bool {
	models := Models()
	gaussian, eisenstein, five := models[0], models[1], models[4]
	var states [9]Point
	var branches [8]bool
	if !Trace(gaussian, Point{0, 2}, Point{}, Point{2, 0}, Point{1, 0},
		states[:], branches[:]) {
		return false
	}
	wantG := [9]Point{{1, 0}, {0, 2}, {0, 1}, {-2, 0}, {-1, 0}, {0, -2}, {0, -1}, {2, 0}, {1, 0}}
	if states != wantG {
		return false
	}
	if !Trace(eisenstein, Point{0, 2}, Point{}, Point{2, 0}, Point{1, 0},
		states[:7], branches[:6]) {
		return false
	}
	wantE := [7]Point{{1, 0}, {0, 2}, {0, 1}, {-2, -2}, {-1, -1}, {2, 0}, {1, 0}}
	for j := range wantE {
		if states[j] != wantE[j] {
			return false
		}
	}
	d := Point{1, 1}
	_, small := ExactQuotient(five, d, Point{3, 0})
	quotient, large := ExactQuotient(five, d, Point{6, 0})
	return !small && large && quotient == (Point{1, -1})
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
		&p.X.Tick.Label, &p.Y.Tick.Label,
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
	p.Title.Padding, p.X.Label.Padding, p.Y.Label.Padding = vg.Points(4), vg.Points(4), vg.Points(4)
	return p
}

// SavePlot pairs a vector PDF with a 300-dpi GitHub preview at identical plot bounds.
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
	preview := vgimg.NewWith(vgimg.UseWH(width, height), vgimg.UseDPI(300))
	p.Draw(draw.Crop(draw.New(preview), margin, -margin, margin, -margin))
	pngPath := strings.TrimSuffix(path, filepath.Ext(path)) + ".png"
	file, err := os.Create(pngPath)
	if err != nil {
		log.Fatal(err)
	}
	_, writeErr = (vgimg.PngCanvas{Canvas: preview}).WriteTo(file)
	closeErr = file.Close()
	if writeErr != nil {
		log.Fatal(writeErr)
	}
	if closeErr != nil {
		log.Fatal(closeErr)
	}
}

// ComplexPoint uses the actual embedding rather than plotting coefficient pairs as C.
func ComplexPoint(m Model, z Point) plotter.XY {
	return plotter.XY{
		X: float64(z.Re) + float64(m.Tau*z.Im)/2,
		Y: math.Sqrt(float64(4*m.Nu-m.Tau*m.Tau)) * float64(z.Im) / 2,
	}
}

// PlotCycle labels each distinct raw tick and separates affine from division inputs.
func PlotCycle(m Model, q, d Point, period int, path string) {
	var states [TraceMax + 1]Point
	var branches [TraceMax]bool
	if !Trace(m, q, Point{}, d, Point{1, 0}, states[:period+1], branches[:period]) {
		log.Fatal("cycle trace exceeded arithmetic bounds")
	}
	p := NewPlot(m.Name+" unit-phase cycle",
		"$\\operatorname{Re}z$", "$\\operatorname{Im}z$")
	pts := make(plotter.XYs, period+1)
	labels := make([]string, period)
	for j := 0; j <= period; j++ {
		pts[j] = ComplexPoint(m, states[j])
	}
	for j := range labels {
		labels[j] = fmt.Sprint(j)
	}
	line, err := plotter.NewLine(pts)
	if err != nil {
		log.Fatal(err)
	}
	line.Color, line.Width = color.Gray{Y: 80}, vg.Points(1.2)
	p.Add(line)
	for _, division := range []bool{false, true} {
		selected := make(plotter.XYs, 0, period)
		for j := 0; j < period; j++ {
			if branches[j] == division {
				selected = append(selected, pts[j])
			}
		}
		scatter, err := plotter.NewScatter(selected)
		if err != nil {
			log.Fatal(err)
		}
		scatter.Radius = vg.Points(4)
		label := "affine input"
		scatter.Color = color.RGBA{R: 20, G: 70, B: 150, A: 255}
		if division {
			label = "division input"
			scatter.Color = color.RGBA{R: 180, G: 80, B: 10, A: 255}
			scatter.Shape = draw.SquareGlyph{}
		}
		p.Add(scatter)
		p.Legend.Add(label, scatter)
	}
	labelled, err := plotter.NewLabels(plotter.XYLabels{XYs: pts[:period], Labels: labels})
	if err != nil {
		log.Fatal(err)
	}
	for j := range labelled.TextStyle {
		labelled.TextStyle[j].Font.Typeface = "LatinModern"
		labelled.TextStyle[j].Font.Size = 12
		labelled.TextStyle[j].Handler = p.TextHandler
	}
	labelled.Offset = vg.Point{X: vg.Points(5), Y: vg.Points(5)}
	p.Add(labelled)
	p.Legend.TextStyle.Font.Size = 12
	p.Legend.TextStyle.Font.Typeface = "LatinModern"
	p.Legend.TextStyle.Handler = p.TextHandler
	p.Legend.Top = true
	p.X.Min, p.X.Max, p.Y.Min, p.Y.Max = -2.6, 2.6, -2.6, 2.6
	SavePlot(p, path, true)
}

// AddHeightTrace plots an exact bounded raw word after converting only the final heights.
func AddHeightTrace(p *plot.Plot, m Model, q, d, seed Point, label string, ink color.Color) {
	var states [TraceMax + 1]Point
	var branches [TraceMax]bool
	if !Trace(m, q, Point{}, d, seed, states[:], branches[:]) {
		log.Fatal("height trace exceeded arithmetic bounds")
	}
	pts := make(plotter.XYs, len(states))
	for j, z := range states {
		pts[j] = plotter.XY{X: float64(j), Y: math.Log1p(float64(Norm(m, z)))}
	}
	line, scatter, err := plotter.NewLinePoints(pts)
	if err != nil {
		log.Fatal(err)
	}
	line.Color, line.Width, scatter.Color, scatter.Radius = ink, vg.Points(1.2), ink, vg.Points(4)
	p.Add(line, scatter)
	p.Legend.Add(label, line, scatter)
}

// PlotDyadicWords shows exact division counts rather than a sampled stochastic frequency.
func PlotDyadicWords(dir string) {
	p := NewPlot("Dyadic instruction counts", "$j$", "$B$")
	inks := [4]color.Color{
		color.RGBA{R: 20, G: 55, B: 125, A: 255},
		color.RGBA{R: 170, G: 65, B: 25, A: 255},
		color.RGBA{R: 30, G: 110, B: 65, A: 255},
		color.RGBA{R: 100, G: 55, B: 120, A: 255},
	}
	for e := 3; e <= 6; e++ {
		hi, lo, divisions := 0, 0, 0
		points := make(plotter.XYs, ValuationMax+1)
		markers := make(plotter.XYs, 0, 6)
		for j := range points {
			points[j] = plotter.XY{X: float64(j), Y: float64(divisions)}
			if j%24 == 0 {
				markers = append(markers, points[j])
			}
			if DyadicGuard(e, hi, lo) {
				hi, lo = hi-(e-1), lo-1
				divisions++
			} else {
				hi, lo = hi+1, lo+1
			}
		}
		line, err := plotter.NewLine(points)
		if err != nil {
			log.Fatal(err)
		}
		dots, err := plotter.NewScatter(markers)
		if err != nil {
			log.Fatal(err)
		}
		line.Color, line.Width = inks[e-3], vg.Points(1.2)
		dots.Color, dots.Radius = inks[e-3], vg.Points(4)
		p.Add(line, dots)
		p.Legend.Add(fmt.Sprintf("D = %d, e = %d", (1<<e)-1, e), line, dots)
	}
	ConfigureLegend(p)
	p.X.Min, p.X.Max, p.Y.Min = 0, ValuationMax, 0
	SavePlot(p, filepath.Join(dir, "DyadicWordCounts.pdf"), false)
}

// FigureDirectory resolves output beside this source, independent of the launch directory.
func FigureDirectory() string {
	_, file, _, ok := runtime.Caller(0)
	if !ok {
		panic("FigureDirectory: source location unavailable")
	}
	return filepath.Join(filepath.Dir(file), "..", "other")
}

// RenderFigures separates a same-norm counterexample from the two phase pictures.
func RenderFigures() {
	dir := FigureDirectory()
	if err := os.MkdirAll(dir, 0755); err != nil {
		log.Fatal(err)
	}
	m := Models()
	PlotCycle(m[0], Point{0, 2}, Point{2, 0}, 8, filepath.Join(dir, "GaussianCycle.pdf"))
	PlotCycle(m[1], Point{0, 2}, Point{2, 0}, 6, filepath.Join(dir, "EisensteinCycle.pdf"))
	p := NewPlot("Equal norms, different dynamics", "$j$", "$\\log(1+N(z))$")
	AddHeightTrace(p, m[0], Point{2, 1}, Point{2, 1}, Point{1, 0},
		"associated divisor: cycle", color.RGBA{R: 20, G: 70, B: 150, A: 255})
	AddHeightTrace(p, m[0], Point{2, 1}, Point{2, -1}, Point{1, 0},
		"conjugate divisor: escape", color.RGBA{R: 180, G: 80, B: 10, A: 255})
	p.Legend.Top, p.Legend.Left = true, true
	p.Legend.TextStyle.Font.Size = 12
	p.Legend.TextStyle.Font.Typeface = "LatinModern"
	p.Legend.TextStyle.Handler = p.TextHandler
	SavePlot(p, filepath.Join(dir, "EqualNormDynamics.pdf"), false)
	p = NewPlot("Quadratic-order guard failure", "$j$", "$\\log(1+N(z))$")
	AddHeightTrace(p, m[4], Point{2, 0}, Point{1, 1}, Point{3, 0},
		"$3,6,1-\\omega,2-2\\omega,\\ldots$", color.RGBA{R: 20, G: 70, B: 150, A: 255})
	p.Legend.Top = true
	p.Legend.TextStyle.Font.Size = 12
	p.Legend.TextStyle.Font.Typeface = "LatinModern"
	p.Legend.TextStyle.Handler = p.TextHandler
	p.Legend.TextStyle.Font.Typeface = "LatinModernMath"
	SavePlot(p, filepath.Join(dir, "QuadraticFiveGuard.pdf"), false)
	PlotParameterFigures(dir)
	PlotDyadicWords(dir)
}

// FirstDivision uses the proved odd-part criterion, not a finite-horizon inference.
func FirstDivision(d, n int64) (int, bool) {
	if d < 1 || d > NuMax {
		panic("FirstDivision: D outside the certified range")
	}
	RequirePoint(Point{n, 0}, PointMax)
	if n == 0 {
		return 0, true
	}
	m, e := d+1, 0
	for m%2 == 0 {
		m /= 2
		e++
	}
	if n%m != 0 {
		return 0, false
	}
	if n < 0 {
		n = -n
	}
	v := 0
	for n%2 == 0 {
		n /= 2
		v++
	}
	if v >= e {
		return 0, true
	}
	return e - v, true
}

// CheckParameterDivision verifies both sides of the first-division certificate on a finite grid.
func CheckParameterDivision() (bool, int) {
	ok, count := true, 0
	for d := int64(1); d <= NuMax; d++ {
		m := Model{Name: "Quadratic", Nu: d}
		for n := int64(-256); n <= 256; n++ {
			a, reaches := FirstDivision(d, n)
			if reaches {
				z := Point{n << a, 0}
				_, div := ExactQuotient(m, Point{1, 1}, z)
				ok = div && ok
				for j := 0; j < a; j++ {
					_, early := ExactQuotient(m, Point{1, 1}, Point{n << j, 0})
					ok = !early && ok
				}
			} else {
				odd := d + 1
				for odd%2 == 0 {
					odd /= 2
				}
				ok = (n%odd != 0) && ok
			}
			count++
		}
	}
	return ok, count
}

// ConfigureLegend applies the same local font metrics to every legend label.
func ConfigureLegend(p *plot.Plot) {
	p.Legend.Top, p.Legend.Left = true, true
	p.Legend.TextStyle.Font.Size = 12
	p.Legend.TextStyle.Font.Typeface = "LatinModern"
	p.Legend.TextStyle.Handler = p.TextHandler
}

// PlotParameterFigures plots a proved density and an explicitly projected integer mesh.
func PlotParameterFigures(dir string) {
	p := NewPlot("First-division density on integer D", "$D$", "$1/\\operatorname{odd}(D+1)$")
	pts := make(plotter.XYs, NuMax)
	for j := range pts {
		odd := int64(j + 2)
		for odd%2 == 0 {
			odd /= 2
		}
		pts[j] = plotter.XY{X: float64(j + 1), Y: 1 / float64(odd)}
	}
	line, dots, err := plotter.NewLinePoints(pts)
	if err != nil {
		log.Fatal(err)
	}
	ink := color.RGBA{R: 20, G: 70, B: 150, A: 255}
	line.Color, line.Width, dots.Color, dots.Radius = ink, vg.Points(1), ink, vg.Points(4)
	p.Add(line, dots)
	p.X.Min, p.X.Max, p.Y.Min, p.Y.Max = 0, 65, 0, 1.05
	SavePlot(p, filepath.Join(dir, "FirstDivisionDensity.pdf"), false)

	p = NewPlot("First-division integer mesh (parallel projection)",
		`$\xi=D+n/2$`, `$\eta=n/2+2h$`)
	const side = 12
	mesh := make(plotter.XYs, side*side)
	finite, never := make(plotter.XYs, 0, side*side), make(plotter.XYs, 0, side*side)
	for d := 1; d <= side; d++ {
		for n := 1; n <= side; n++ {
			a, reaches := FirstDivision(int64(d), int64(n))
			h := 0
			if reaches {
				h = a + 1
			}
			xy := plotter.XY{X: float64(d) + float64(n)/2, Y: float64(n)/2 + 2*float64(h)}
			mesh[(d-1)*side+n-1] = xy
			if reaches {
				finite = append(finite, xy)
			} else {
				never = append(never, xy)
			}
		}
	}
	// Lines join discrete samples only; they do not assert a continuous D-parameter law.
	for d := 0; d < side; d++ {
		row, err := plotter.NewLine(mesh[d*side : (d+1)*side])
		if err != nil {
			log.Fatal(err)
		}
		row.Color, row.Width = color.RGBA{R: 160, G: 170, B: 180, A: 255}, vg.Points(0.5)
		p.Add(row)
	}
	for n := 0; n < side; n++ {
		column := make(plotter.XYs, side)
		for d := range column {
			column[d] = mesh[d*side+n]
		}
		line, err := plotter.NewLine(column)
		if err != nil {
			log.Fatal(err)
		}
		line.Color, line.Width = color.RGBA{R: 200, G: 200, B: 200, A: 255}, vg.Points(0.5)
		p.Add(line)
	}
	for i, points := range []plotter.XYs{finite, never} {
		dots, err := plotter.NewScatter(points)
		if err != nil {
			log.Fatal(err)
		}
		dots.Radius = vg.Points(4)
		if i == 0 {
			dots.Color = ink
			p.Legend.Add("first division: h = a + 1", dots)
		} else {
			dots.Color = color.RGBA{R: 180, G: 80, B: 10, A: 255}
			dots.Shape = draw.SquareGlyph{}
			p.Legend.Add("never divides: h = 0", dots)
		}
		p.Add(dots)
	}
	ConfigureLegend(p)
	SavePlot(p, filepath.Join(dir, "FirstDivisionSurface.pdf"), false)
}

// main refuses failed finite certificates before emitting any research figure.
func main() {
	ok, count := RunCertificate()
	if !ok || !Witnesses() {
		log.Fatal("quadratic arithmetic certificate failed")
	}
	RenderFigures()
	fmt.Printf("finite arithmetic checks passed: %d; exact orbit witnesses passed\n", count)
}
