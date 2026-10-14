// SPDX-License-Identifier: CC-BY-4.0
// This bounded certificate keeps the raw integer cycle separate from coefficient reduction.
package main

import (
	"encoding/json"
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
	ResonancePrime int64 = 139
	ControlPrime   int64 = 137
	Edges                = 18
	Chunks               = 4
)

// Coefficient records a+b*i in the genuine Gaussian extension of the 139-element field.
type Coefficient struct {
	Re, Im int64
}

// Workspace holds one cycle's coefficients and reusable finite-elimination matrix.
type Workspace struct {
	Weights, Offsets [Edges]int64
	Matrix           [Edges][Edges]int64
}

// FieldCensus reports exact finite arithmetic, not a census of raw Collatz residues.
type FieldCensus struct {
	Characteristic int64 `json:"characteristic"`
	Elements       int   `json:"elements"`
	FrobeniusImage int   `json:"frobenius_images"`
	FrobeniusFixed int   `json:"frobenius_fixed"`
	DefiningRoots  int   `json:"defining_roots"`
	NonzeroInverse int   `json:"nonzero_inverses"`
	NormInvariant  int   `json:"norm_invariant_checks"`
}

// ChunkResult owns its counters and failure, preventing shared writes in the hot loops.
type ChunkResult struct {
	Fixed, Roots, Inverses, Norms int
	Failure                       string
}

// Cache separates each chunk's image marks, even if a faulty map creates collisions.
type Cache struct {
	Seen    [Chunks][19321]bool
	Results [Chunks]ChunkResult
}

// CycleReport retains the ordered coefficients, actual offset and computed quotient dimension.
type CycleReport struct {
	Characteristic int64 `json:"characteristic"`
	Holonomy       int64 `json:"holonomy"`
	OffsetPeriod   int64 `json:"actual_offset_period"`
	UnitPeriod     int64 `json:"last_edge_unit_period"`
	Rank           int   `json:"twisted_incidence_rank"`
	H1Dimension    int   `json:"h1_dimension"`
	ActualExact    bool  `json:"actual_offset_exact"`
}

// Report combines the prime-field controls with the independent quadratic arithmetic census.
type Report struct {
	States       [Edges]int64   `json:"raw_states"`
	RawLegal     bool           `json:"raw_cycle_legal"`
	Distinct     bool           `json:"raw_states_distinct"`
	Affine       int            `json:"affine_ticks"`
	Division     int            `json:"division_ticks"`
	Defect       int64          `json:"integer_power_defect"`
	Coefficients [2]CycleReport `json:"coefficient_fields"`
	Extension    FieldCensus    `json:"gaussian_extension"`
}

// States returns a fresh value array, so a caller cannot mutate the shared marked cycle.
func States() [Edges]int64 {
	return [Edges]int64{
		17, 50, 25, 74, 37, 110, 55, 164, 82, 41, 122, 61, 182, 91, 272, 136, 68, 34,
	}
}

// AffineEdge marks the same raw clock positions used in the checked Lean word.
func AffineEdge(j int) bool {
	if j < 0 || j >= Edges {
		panic("cycle edge is outside the marked eighteen-edge word")
	}
	switch j {
	case 0, 2, 4, 6, 9, 11, 13:
		return true
	default:
		return false
	}
}

// Residue normalizes signed integers without changing the integer-state divisibility guard.
func Residue(x, p int64) int64 {
	r := x % p
	if r < 0 {
		r += p
	}
	return r
}

// RequireCharacteristic keeps this finite certificate within its two proved prime moduli.
func RequireCharacteristic(p int64) {
	if p != ResonancePrime && p != ControlPrime {
		panic("cochain characteristic must be the certified prime 137 or 139")
	}
}

// ScalarPower uses binary powering on bounded normalized prime-field coefficients.
func ScalarPower(x int64, exponent uint64, p int64) int64 {
	RequireCharacteristic(p)
	x = Residue(x, p)
	result := int64(1)
	for exponent > 0 {
		if exponent&1 != 0 {
			result = result * x % p
		}
		x = x * x % p
		exponent >>= 1
	}
	return result
}

// Initialize preserves the marked edge order and constructs the genuine twisted incidence.
func Initialize(w *Workspace, p int64) {
	RequireCharacteristic(p)
	w.Matrix = [Edges][Edges]int64{}
	for j := 0; j < Edges; j++ {
		w.Weights[j], w.Offsets[j] = (p+1)/2, 0
		if AffineEdge(j) {
			w.Weights[j], w.Offsets[j] = 3, p-1
		}
		w.Matrix[j][j] = Residue(-w.Weights[j], p)
		w.Matrix[j][(j+1)%Edges] = 1
	}
}

// WeightedPeriod executes ordered offset transport, using one scalar accumulator.
func WeightedPeriod(weights, offsets [Edges]int64, p int64) int64 {
	RequireCharacteristic(p)
	b := int64(0)
	for j := 0; j < Edges; j++ {
		b = (weights[j]*b + offsets[j]) % p
	}
	return b
}

// MatrixRank eliminates the fixed matrix in place; no allocation occurs in its row loops.
func MatrixRank(w *Workspace, p int64) int {
	RequireCharacteristic(p)
	rank := 0
	for col := 0; col < Edges && rank < Edges; col++ {
		pivot := rank
		for pivot < Edges && w.Matrix[pivot][col] == 0 {
			pivot++
		}
		if pivot == Edges {
			continue
		}
		w.Matrix[rank], w.Matrix[pivot] = w.Matrix[pivot], w.Matrix[rank]
		inverse := ScalarPower(w.Matrix[rank][col], uint64(p-2), p)
		for j := col; j < Edges; j++ {
			w.Matrix[rank][j] = w.Matrix[rank][j] * inverse % p
		}
		for row := 0; row < Edges; row++ {
			if row == rank {
				continue
			}
			factor := w.Matrix[row][col]
			for j := col; j < Edges; j++ {
				w.Matrix[row][j] = Residue(
					w.Matrix[row][j]-factor*w.Matrix[rank][j], p,
				)
			}
		}
		rank++
	}
	return rank
}

// InspectCycle contrasts neutral and nonneutral coefficients without re-running residue guards.
func InspectCycle(p int64) CycleReport {
	var w Workspace
	Initialize(&w, p)
	h := int64(1)
	actual := true
	states := States()
	var unit [Edges]int64
	unit[Edges-1] = 1
	for j := 0; j < Edges; j++ {
		h = h * w.Weights[j] % p
		actual = actual && Residue(states[(j+1)%Edges], p) ==
			Residue(w.Weights[j]*Residue(states[j], p)+w.Offsets[j], p)
	}
	b := WeightedPeriod(w.Weights, w.Offsets, p)
	u := WeightedPeriod(w.Weights, unit, p)
	rank := MatrixRank(&w, p)
	return CycleReport{p, h, b, u, rank, Edges - rank, actual}
}

// Normalize bounds both coefficients before any Gaussian multiplication.
func Normalize(z Coefficient) Coefficient {
	return Coefficient{Residue(z.Re, ResonancePrime), Residue(z.Im, ResonancePrime)}
}

// GaussianMultiply uses i squared equals minus one; every product is below 40,000 in magnitude.
func GaussianMultiply(z, w Coefficient) Coefficient {
	z, w = Normalize(z), Normalize(w)
	return Normalize(Coefficient{z.Re*w.Re - z.Im*w.Im, z.Re*w.Im + z.Im*w.Re})
}

// GaussianPower works in the extension ring, not componentwise in a Cartesian product.
func GaussianPower(z Coefficient, exponent uint64) Coefficient {
	z = Normalize(z)
	result := Coefficient{1, 0}
	for exponent > 0 {
		if exponent&1 != 0 {
			result = GaussianMultiply(result, z)
		}
		z = GaussianMultiply(z, z)
		exponent >>= 1
	}
	return result
}

// Conjugate is the explicit involution a+b*i maps to a-b*i.
func Conjugate(z Coefficient) Coefficient {
	z = Normalize(z)
	return Normalize(Coefficient{z.Re, -z.Im})
}

// GaussianInverse uses the nonzero norm in the certified inert Gaussian extension.
func GaussianInverse(z Coefficient) (Coefficient, bool) {
	z = Normalize(z)
	norm := Residue(z.Re*z.Re+z.Im*z.Im, ResonancePrime)
	if norm == 0 {
		return Coefficient{}, false
	}
	inverse := ScalarPower(norm, uint64(ResonancePrime-2), ResonancePrime)
	return Normalize(Coefficient{z.Re * inverse, -z.Im * inverse}), true
}

// CheckFieldChunk exhausts disjoint imaginary-coordinate rows with preallocated image marks.
func CheckFieldChunk(cache *Cache, chunk int, done *sync.WaitGroup) {
	defer done.Done()
	lo := int64(chunk) * ResonancePrime / Chunks
	hi := int64(chunk+1) * ResonancePrime / Chunks
	result := &cache.Results[chunk]
	for im := lo; im < hi; im++ {
		for re := int64(0); re < ResonancePrime; re++ {
			z := Coefficient{re, im}
			f := GaussianPower(z, uint64(ResonancePrime))
			// Failure diagnostics allocate only on a rejected arithmetic obligation.
			if f != Conjugate(z) ||
				GaussianPower(f, uint64(ResonancePrime)) != z {
				result.Failure = fmt.Sprintf("Frobenius failed at (%d,%d)", re, im)
				return
			}
			norm := GaussianMultiply(z, Conjugate(z))
			if norm != (Coefficient{GaussianNorm(z), 0}) ||
				GaussianNorm(f) != GaussianNorm(z) {
				result.Failure = fmt.Sprintf("norm failed at (%d,%d)", re, im)
				return
			}
			result.Norms++
			cache.Seen[chunk][int(f.Re+ResonancePrime*f.Im)] = true
			if f == z {
				result.Fixed++
			}
			if GaussianMultiply(z, z) == (Coefficient{ResonancePrime - 1, 0}) {
				result.Roots++
			}
			inverse, ok := GaussianInverse(z)
			if z == (Coefficient{}) {
				if ok {
					result.Failure = "zero unexpectedly has an inverse"
					return
				}
				continue
			}
			if !ok || GaussianMultiply(z, inverse) != (Coefficient{1, 0}) ||
				inverse != GaussianPower(z, 19319) {
				result.Failure = fmt.Sprintf("inverse failed at (%d,%d)", re, im)
				return
			}
			result.Inverses++
		}
	}
}

// RunFieldCensus joins all independent chunks and counts the union without shared bitmap writes.
func RunFieldCensus() (FieldCensus, error) {
	var cache Cache
	var done sync.WaitGroup
	done.Add(Chunks)
	for chunk := 0; chunk < Chunks; chunk++ {
		go CheckFieldChunk(&cache, chunk, &done)
	}
	done.Wait()
	census := FieldCensus{Characteristic: ResonancePrime, Elements: 19321}
	for chunk := 0; chunk < Chunks; chunk++ {
		r := cache.Results[chunk]
		if r.Failure != "" {
			return FieldCensus{}, fmt.Errorf("chunk %d: %s", chunk, r.Failure)
		}
		census.FrobeniusFixed += r.Fixed
		census.DefiningRoots += r.Roots
		census.NonzeroInverse += r.Inverses
		census.NormInvariant += r.Norms
	}
	for index := 0; index < 19321; index++ {
		present := false
		for chunk := 0; chunk < Chunks; chunk++ {
			present = present || cache.Seen[chunk][index]
		}
		if present {
			census.FrobeniusImage++
		}
	}
	return census, nil
}

// IntegerPowerDefect computes within the fixed word budget, rather than copying a target answer.
func IntegerPowerDefect(affine, division int) int64 {
	if affine < 0 || affine > 7 || division < 0 || division > 11 {
		panic("integer defect is outside the certified marked-word budget")
	}
	a, d := int64(1), int64(1)
	for j := 0; j < affine; j++ {
		a *= 3
	}
	for j := 0; j < division; j++ {
		d *= 2
	}
	return a - d
}

// BuildReport verifies the raw states and independent finite controls before publishing counts.
func BuildReport() (Report, error) {
	report := Report{States: States(), RawLegal: true, Distinct: true}
	for j, state := range report.States {
		next := int64(0)
		if state%2 == 0 {
			next = state / 2
			report.Division++
		} else {
			next = 3*state - 1
			report.Affine++
		}
		report.RawLegal = report.RawLegal && next == report.States[(j+1)%Edges]
		for k := 0; k < j; k++ {
			report.Distinct = report.Distinct && state != report.States[k]
		}
	}
	report.Defect = IntegerPowerDefect(report.Affine, report.Division)
	report.Coefficients = [2]CycleReport{InspectCycle(ControlPrime), InspectCycle(ResonancePrime)}
	census, err := RunFieldCensus()
	if err != nil {
		return Report{}, err
	}
	report.Extension = census
	a, b := report.Coefficients[0], report.Coefficients[1]
	if !report.RawLegal || !report.Distinct || report.Affine != 7 || report.Division != 11 ||
		report.Defect != 139 ||
		a.Holonomy == 1 || a.Rank != 18 || b.Holonomy != 1 || b.Rank != 17 ||
		!a.ActualExact || !b.ActualExact ||
		a.OffsetPeriod != Residue((1-a.Holonomy)*report.States[0], ControlPrime) ||
		b.OffsetPeriod != 0 ||
		a.UnitPeriod != 1 || b.UnitPeriod != 1 ||
		census.FrobeniusImage != 19321 || census.FrobeniusFixed != 139 ||
		census.DefiningRoots != 2 || census.NonzeroInverse != 19320 ||
		census.NormInvariant != 19321 {
		return Report{}, fmt.Errorf("marked-cycle or field census contract failed")
	}
	return report, nil
}

// GaussianNorm computes the exact prime-field norm used to color quotient coordinates.
func GaussianNorm(z Coefficient) int64 {
	z = Normalize(z)
	return Residue(z.Re*z.Re+z.Im*z.Im, ResonancePrime)
}

// NormColor interpolates five explicit print-visible anchors on representatives 0 through 138.
func NormColor(norm int64) color.RGBA {
	if norm < 0 || norm >= ResonancePrime {
		panic("norm color requires a normalized coefficient")
	}
	anchors := [5][3]int64{{68, 1, 84}, {59, 82, 139}, {33, 145, 140},
		{94, 201, 98}, {253, 231, 37}}
	if norm == ResonancePrime-1 {
		return color.RGBA{253, 231, 37, 255}
	}
	position := norm * 4
	index, remainder := position/138, position%138
	mix := func(component int) uint8 {
		return uint8((anchors[index][component]*(138-remainder) +
			anchors[index+1][component]*remainder) / 138)
	}
	return color.RGBA{mix(0), mix(1), mix(2), 255}
}

// NormPanel depicts finite-field representatives, not a subset with a canonical complex metric.
type NormPanel struct{}

// Plot gives each of the 19,321 exact quotient coordinates one cell and reuses its path buffer.
func (NormPanel) Plot(c draw.Canvas, p *plot.Plot) {
	trX, trY := p.Transforms(&c)
	path := make(vg.Path, 0, 5)
	corners := [4][2]float64{{-.5, -.5}, {.5, -.5}, {.5, .5}, {-.5, .5}}
	for im := int64(-69); im <= 69; im++ {
		for re := int64(-69); re <= 69; re++ {
			path = path[:0]
			for j, corner := range corners {
				point := vg.Point{X: trX(float64(re) + corner[0]),
					Y: trY(float64(im) + corner[1])}
				if j == 0 {
					path.Move(point)
				} else {
					path.Line(point)
				}
			}
			path.Close()
			c.SetColor(NormColor(GaussianNorm(Coefficient{re, im})))
			c.Fill(path)
		}
	}
}

// PlotNorm makes the fixed prime-field line and conjugate coordinate pairs visible.
func PlotNorm(out string) {
	p := NewPlot("Frobenius on 19,321 classes", "$u$", "$v$")
	// Reserve an uncolored strip so the legend hides no finite-field coordinate.
	p.X.Min, p.X.Max, p.Y.Min, p.Y.Max = -69.5, 69.5, -69.5, 119.5
	ticks := plot.ConstantTicks{
		{Value: -60, Label: "-60"}, {Value: -30, Label: "-30"},
		{Value: 0, Label: "0"}, {Value: 30, Label: "30"}, {Value: 60, Label: "60"},
	}
	p.X.Tick.Marker, p.Y.Tick.Marker = ticks, ticks
	p.Add(NormPanel{})
	fixed, err := plotter.NewLine(plotter.XYs{{X: -69.5, Y: 0}, {X: 69.5, Y: 0}})
	if err != nil {
		log.Fatal(err)
	}
	fixed.Color, fixed.Width = color.RGBA{255, 90, 60, 255}, vg.Points(1.5)
	p.Add(fixed)
	p.Legend.Add("139 fixed classes", fixed)
	for _, n := range [3]int64{0, 69, 138} {
		key, err := plotter.NewScatter(plotter.XYs{{X: 0, Y: 0}})
		if err != nil {
			log.Fatal(err)
		}
		key.Color, key.Radius = NormColor(n), vg.Points(4)
		p.Legend.Add(fmt.Sprintf("$N(z)=%d$", n), key)
	}
	p.Legend.Top, p.Legend.Left = true, true
	SavePanel(p, filepath.Join(out, "Galois139"), true)
}

// PlotWord separates the true raw return from its nonneutral characteristic-zero multiplier.
func PlotWord(out string) {
	states := States()
	values, weights := make(plotter.XYs, Edges+1), make(plotter.XYs, Edges+1)
	factor := float64(1)
	for j := 0; j <= Edges; j++ {
		values[j] = plotter.XY{X: float64(j),
			Y: math.Log2(float64(states[j%Edges]) / float64(states[0]))}
		weights[j] = plotter.XY{X: float64(j), Y: math.Log2(factor)}
		if j < Edges {
			if AffineEdge(j) {
				factor *= 3
			} else {
				factor /= 2
			}
		}
	}
	p := NewPlot("Raw return versus word holonomy", "$j$", `$\log(r)/\log(2)$`)
	p.X.Min, p.X.Max, p.Y.Min, p.Y.Max = -.5, 18.5, -.4, 4.7
	p.X.Tick.Marker = plot.ConstantTicks{
		{Value: 0, Label: "0"}, {Value: 3, Label: "3"}, {Value: 6, Label: "6"},
		{Value: 9, Label: "9"}, {Value: 12, Label: "12"},
		{Value: 15, Label: "15"}, {Value: 18, Label: "18"},
	}
	for j, points := range [2]plotter.XYs{values, weights} {
		line, scatter, err := plotter.NewLinePoints(points)
		if err != nil {
			log.Fatal(err)
		}
		col := [2]color.RGBA{{180, 30, 55, 255}, {30, 80, 190, 255}}[j]
		line.Color, line.Width = col, vg.Points(1.5)
		scatter.Color, scatter.Radius = col, vg.Points(4)
		p.Add(line, scatter)
		p.Legend.Add([2]string{"raw value / 17", "prefix multiplier"}[j], line, scatter)
	}
	p.Legend.Top, p.Legend.Left = true, true
	SavePanel(p, filepath.Join(out, "WordHolonomy"), false)
}

// PlotDefect magnifies the offset correction that is small at the full-profile return.
func PlotDefect(out string) {
	states := States()
	points := make(plotter.XYs, Edges+1)
	offset := float64(0)
	for j := 0; j <= Edges; j++ {
		points[j] = plotter.XY{X: float64(j), Y: -offset / float64(states[0])}
		if j < Edges {
			if AffineEdge(j) {
				offset = 3*offset - 1
			} else {
				offset /= 2
			}
		}
	}
	p := NewPlot("Offset correction along the marked word", "$j$", "$-B/17$")
	p.X.Min, p.X.Max, p.Y.Min, p.Y.Max = -.5, 18.5, -.04, 1.16
	p.X.Tick.Marker = plot.ConstantTicks{
		{Value: 0, Label: "0"}, {Value: 3, Label: "3"}, {Value: 6, Label: "6"},
		{Value: 9, Label: "9"}, {Value: 12, Label: "12"},
		{Value: 15, Label: "15"}, {Value: 18, Label: "18"},
	}
	line, scatter, err := plotter.NewLinePoints(points)
	if err != nil {
		log.Fatal(err)
	}
	line.Color, scatter.Color = color.RGBA{30, 80, 190, 255}, color.RGBA{30, 80, 190, 255}
	line.Width, scatter.Radius = vg.Points(1.5), vg.Points(4)
	p.Add(line, scatter)
	p.Legend.Add("return correction = 139/2048", line, scatter)
	p.Legend.Top, p.Legend.Left = true, true
	SavePanel(p, filepath.Join(out, "OffsetCorrection"), false)
}

// GenerateFigures writes local deterministic data and figures after the exact contract passes.
func GenerateFigures(report Report) error {
	_, source, _, ok := runtime.Caller(0)
	if !ok {
		return fmt.Errorf("figure source location unavailable")
	}
	out := filepath.Join(filepath.Dir(source), "..", "other")
	if err := os.MkdirAll(out, 0755); err != nil {
		return err
	}
	data, err := json.MarshalIndent(report, "", "  ")
	if err != nil {
		return err
	}
	dataPath := filepath.Join(out, "CycleResonance.json")
	if err := os.WriteFile(dataPath, append(data, '\n'), 0644); err != nil {
		return err
	}
	PlotNorm(out)
	PlotWord(out)
	PlotDefect(out)
	return nil
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
// Only the eight documented TeX expressions are supported. Other math fails loudly.
type MathLabels struct {
	text.Plain
}

// LabelText accepts exactly the eight mathematical labels used by these figures.
func LabelText(txt string) (string, bool) {
	if strings.ContainsAny(txt, "\r\n") {
		panic("multiline labels are not supported")
	}
	switch txt {
	case `$u$`:
		return "𝑢", true
	case `$v$`:
		return "𝑣", true
	case `$j$`:
		return "𝑗", true
	case `$\log(r)/\log(2)$`:
		return "log(𝑟)/log(2)", true
	case `$-B/17$`:
		return "−𝐵/17", true
	case `$N(z)=0$`:
		return "𝑁(𝑧)=0", true
	case `$N(z)=69$`:
		return "𝑁(𝑧)=69", true
	case `$N(z)=138$`:
		return "𝑁(𝑧)=138", true
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
		// Check the complete glyph repertoire, including every mathematical descender.
		for _, r := range "𝑢𝑣𝑗log𝑟𝑁(𝑧)/=2069138−𝐵7" {
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
	ext := h.Extents(fnt)
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

// SavePanel keeps a vector PDF and a 300-dpi preview with the same aspect and font metrics.
func SavePanel(p *plot.Plot, base string, square bool) {
	SavePlot(p, base+".pdf", square)
	width, height := 6*vg.Inch, 4*vg.Inch
	if square {
		width, height = 5*vg.Inch, 5*vg.Inch
	}
	canvas := vgimg.NewWith(vgimg.UseWH(width, height), vgimg.UseDPI(300))
	margin := vg.Points(4)
	p.Draw(draw.Crop(draw.New(canvas), margin, -margin, margin, -margin))
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

// main emits the finite report and figures, never a raw finite-field orbit map.
func main() {
	report, err := BuildReport()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := GenerateFigures(report); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	encoder := json.NewEncoder(os.Stdout)
	encoder.SetIndent("", "  ")
	if err := encoder.Encode(report); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
