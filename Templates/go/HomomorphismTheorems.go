// HomomorphismTheorems.go
// Computational check of the first isomorphism theorem on ℤ/12ℤ → ℤ/4ℤ.
package main

import (
	"fmt"
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
	"gonum.org/v1/gonum/blas/gonum"
	"gonum.org/v1/gonum/floats"
	"gonum.org/v1/gonum/mat"
	"gonum.org/v1/gonum/optimize"
	"gonum.org/v1/gonum/stat"
	"gonum.org/v1/plot"
	"gonum.org/v1/plot/font"
	"gonum.org/v1/plot/plotter"
	"gonum.org/v1/plot/text"
	"gonum.org/v1/plot/vg"
	"gonum.org/v1/plot/vg/draw"
	"gonum.org/v1/plot/vg/vgpdf"
)

// Workspace holds domain and image values for a cyclic-group map.
type Workspace struct {
	Domain []int
	Values []int
}

// Cache holds kernel, image, and reusable scratch for a homomorphism.
type Cache struct {
	Kernel  []int
	Image   []int
	seen    []bool
	fibers  []float64
	scratch []float64
}

// ApplyModHom writes canonical residues into values using disjoint worker chunks.
// Require mod > 0, len(values) >= len(domain), and no partial overlap of the slices.
// Identical slices are allowed; values beyond len(domain) are left unchanged.
func ApplyModHom(values, domain []int, mod int) {
	n := len(domain)
	if mod <= 0 || len(values) < n {
		panic("ApplyModHom: positive modulus and sufficient output length required")
	}
	values = values[:n]
	domain = domain[:n]
	workers := runtime.GOMAXPROCS(0)
	if workers < 1 {
		workers = 1
	}
	chunk := (n + workers - 1) / workers
	var wg sync.WaitGroup
	for start := 0; start < n; start += chunk {
		end := start + chunk
		if end > n {
			end = n
		}
		wg.Add(1)
		// Each worker owns its output slice, including when values aliases domain.
		go func(lo, hi int) {
			defer wg.Done()
			d := domain[lo:hi]
			v := values[lo:hi]
			d = d[:len(d)]
			v = v[:len(d)]
			for i := 0; i < len(d); i++ {
				r := d[i] % mod
				if r < 0 {
					r += mod
				}
				v[i] = r
			}
		}(start, end)
	}
	wg.Wait()
}

// KernelFill records elements sent to identity, reusing Kernel.
// Require len(values) >= len(domain); cache methods are not safe for concurrent use.
func (c *Cache) KernelFill(domain, values []int, identity int) {
	k := c.Kernel[:0]
	if cap(k) < len(domain) {
		k = make([]int, 0, len(domain))
	}
	domain = domain[:len(domain)]
	values = values[:len(values)]
	n := len(domain)
	values = values[:n]
	for i := 0; i < n; i++ {
		if values[i] == identity {
			k = append(k, domain[i])
		}
	}
	c.Kernel = k
}

// ImageFill records unique canonical residues in encounter order, reusing Image.
// Require mod > 0 and values in 0..mod-1; invalid residues panic instead of disappearing.
func (c *Cache) ImageFill(values []int, mod int) {
	if mod <= 0 {
		panic("ImageFill: positive modulus required")
	}
	if cap(c.seen) < mod {
		c.seen = make([]bool, mod)
	} else {
		c.seen = c.seen[:mod]
		for i := range c.seen {
			c.seen[i] = false
		}
	}
	img := c.Image[:0]
	if cap(img) < mod {
		img = make([]int, 0, mod)
	}
	values = values[:len(values)]
	for i := 0; i < len(values); i++ {
		v := values[i]
		if v < 0 || v >= mod {
			panic("ImageFill: value outside canonical residue range")
		}
		if !c.seen[v] {
			c.seen[v] = true
			img = append(img, v)
		}
	}
	c.Image = img
}

// FirstIsoCardinalities checks the finite cardinality identity without multiplication overflow.
// This necessary check alone does not prove that the supplied data defines a homomorphism.
func FirstIsoCardinalities(c *Cache, order int) bool {
	k := len(c.Kernel)
	im := len(c.Image)
	return order > 0 && k > 0 && order%k == 0 && order/k == im
}

// FiberSizes records |φ^{-1}(y)| for every canonical residue, reusing the buffer.
// Require mod > 0 and values in 0..mod-1.
func (c *Cache) FiberSizes(values []int, mod int) {
	if mod <= 0 {
		panic("FiberSizes: positive modulus required")
	}
	if cap(c.fibers) < mod {
		c.fibers = make([]float64, mod)
	} else {
		c.fibers = c.fibers[:mod]
	}
	for i := range c.fibers {
		c.fibers[i] = 0
	}
	values = values[:len(values)]
	for i := 0; i < len(values); i++ {
		v := values[i]
		if v < 0 || v >= mod {
			panic("FiberSizes: value outside canonical residue range")
		}
		c.fibers[v]++
	}
}

// AsFloat returns cache-owned scratch, invalidated by the next AsFloat call.
func (c *Cache) AsFloat(src []int) []float64 {
	n := len(src)
	if cap(c.scratch) < n {
		c.scratch = make([]float64, n)
	} else {
		c.scratch = c.scratch[:n]
	}
	src = src[:n]
	out := c.scratch
	out = out[:n]
	for i := 0; i < n; i++ {
		out[i] = float64(src[i])
	}
	return out
}

// FitConstant fits a least-squares constant to finite, nonempty data via Gonum optimize.
func FitConstant(xs []float64) float64 {
	if len(xs) == 0 {
		panic("FitConstant: nonempty data required")
	}
	for _, x := range xs {
		if math.IsNaN(x) || math.IsInf(x, 0) {
			panic("FitConstant: finite data required")
		}
	}
	problem := optimize.Problem{
		// The minimizer of this quadratic should equal the arithmetic mean.
		Func: func(x []float64) float64 {
			mu := x[0]
			s := 0.0
			ys := xs
			ys = ys[:len(ys)]
			for i := 0; i < len(ys); i++ {
				d := ys[i] - mu
				s += d * d
			}
			return s
		},
	}
	res, err := optimize.Minimize(problem, []float64{0}, nil, nil)
	if err != nil {
		log.Fatal(err)
	}
	return res.X[0]
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
// Only the three demonstrated TeX expressions are supported. Other math fails loudly.
type MathLabels struct {
	text.Plain
}

// LabelText converts three single-line TeX expressions to equivalent Unicode math.
func LabelText(txt string) (string, bool) {
	if strings.ContainsAny(txt, "\r\n") {
		panic("multiline labels are not supported")
	}
	switch txt {
	case `$|G|/|\ker\varphi|=|\operatorname{im}\varphi|$`:
		return "|𝐺|/|ker 𝜑| = |im 𝜑|", true
	case `$g\in\mathbb{Z}/12\mathbb{Z}$`:
		return "𝑔 ∈ ℤ/12ℤ", true
	case `$\varphi(g)\in\mathbb{Z}/4\mathbb{Z}$`:
		return "𝜑(𝑔) ∈ ℤ/4ℤ", true
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
		// This is the complete glyph repertoire of the three supported expressions.
		for _, r := range "|𝐺/ker 𝜑=im𝑔∈ℤ124()" {
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

// PlotFirstIso writes the canonical ℤ/12ℤ → ℤ/4ℤ example as a 3:2 PDF.
// Reject other data rather than silently labelling it as this specific map.
func PlotFirstIso(ws *Workspace, out string) {
	if ws == nil || len(ws.Domain) != 12 || len(ws.Values) != 12 {
		panic("PlotFirstIso: the canonical 12-to-4 workspace is required")
	}
	n := len(ws.Domain)
	pts := make(plotter.XYs, n)
	ws.Domain = ws.Domain[:n]
	ws.Values = ws.Values[:n]
	for i := 0; i < n; i++ {
		if ws.Domain[i] != i || ws.Values[i] != i%4 {
			panic("PlotFirstIso: data does not match the labelled cyclic reduction")
		}
		pts[i].X = float64(ws.Domain[i])
		pts[i].Y = float64(ws.Values[i])
	}
	p := plot.New()
	RegisterLatinModern(p)
	p.Title.Text = `$|G|/|\ker\varphi|=|\operatorname{im}\varphi|$`
	p.Title.TextStyle.Font.Size = 16
	p.X.Label.Text = `$g\in\mathbb{Z}/12\mathbb{Z}$`
	p.X.Label.TextStyle.Font.Size = 14
	p.Y.Label.Text = `$\varphi(g)\in\mathbb{Z}/4\mathbb{Z}$`
	p.Y.Label.TextStyle.Font.Size = 14
	p.Title.Padding = vg.Points(4)
	p.X.Label.Padding = vg.Points(4)
	p.Y.Label.Padding = vg.Points(4)
	p.X.Tick.Label.Font.Size = 12
	p.Y.Tick.Label.Font.Size = 12
	s, err := plotter.NewScatter(pts)
	if err != nil {
		log.Fatal(err)
	}
	s.Radius = vg.Points(4)
	p.X.Min, p.X.Max = -0.5, 11.5
	p.Y.Min, p.Y.Max = -0.25, 3.25
	xticks := make(plot.ConstantTicks, 12)
	for i := range xticks {
		xticks[i] = plot.Tick{Value: float64(i), Label: fmt.Sprint(i)}
	}
	p.X.Tick.Marker = xticks
	p.Y.Tick.Marker = plot.ConstantTicks{
		{Value: 0, Label: "0"}, {Value: 1, Label: "1"},
		{Value: 2, Label: "2"}, {Value: 3, Label: "3"},
	}
	p.Add(s)
	// Keep glyphs away from the page boundary without changing the PDF's dimensions.
	canvas := vgpdf.New(6*vg.Inch, 4*vg.Inch)
	margin := vg.Points(4)
	p.Draw(draw.Crop(draw.New(canvas), margin, -margin, margin, -margin))
	file, err := os.Create(out)
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

// PlotPath returns Templates/other/FirstIsoFibers.pdf next to this file.
func PlotPath() string {
	_, file, _, ok := runtime.Caller(0)
	if !ok {
		return filepath.Join("Templates", "other", "FirstIsoFibers.pdf")
	}
	return filepath.Join(
		filepath.Dir(file),
		"..",
		"other",
		"FirstIsoFibers.pdf",
	)
}

// main checks the cyclic homomorphism, all fibers, and Gonum numerics before plotting.
func main() {
	const domainMod = 12
	const codomainMod = 4
	if domainMod%codomainMod != 0 {
		log.Fatal("cyclic reduction is not well-defined for these moduli")
	}
	domain := make([]int, domainMod)
	values := make([]int, domainMod)
	for i := 0; i < domainMod; i++ {
		domain[i] = i
	}
	ApplyModHom(values, domain, codomainMod)
	// Exhaustively check preservation of addition in this finite cyclic group.
	for i := 0; i < domainMod; i++ {
		for j := 0; j < domainMod; j++ {
			if values[(i+j)%domainMod] != (values[i]+values[j])%codomainMod {
				log.Fatal("cyclic addition was not preserved")
			}
		}
	}
	ws := Workspace{Domain: domain, Values: values}
	cache := Cache{
		Kernel:  make([]int, 0, domainMod),
		Image:   make([]int, 0, codomainMod),
		seen:    make([]bool, codomainMod),
		fibers:  make([]float64, codomainMod),
		scratch: make([]float64, domainMod),
	}
	cache.KernelFill(ws.Domain, ws.Values, 0)
	cache.ImageFill(ws.Values, codomainMod)
	if !FirstIsoCardinalities(&cache, domainMod) {
		log.Fatal("first isomorphism cardinalities failed")
	}
	cache.FiberSizes(ws.Values, codomainMod)
	for _, size := range cache.fibers {
		if size != float64(len(cache.Kernel)) {
			log.Fatal("fiber size differs from kernel cardinality")
		}
	}
	meanFiber := stat.Mean(cache.fibers, nil)
	xs := cache.AsFloat(ws.Values)
	mean := floats.Sum(xs) / float64(len(xs))
	vec := mat.NewVecDense(len(xs), xs)
	impl := gonum.Implementation{}
	norm := impl.Dnrm2(len(xs), xs, 1)
	mu := FitConstant(xs)
	if meanFiber != 3 || mean != 1.5 || math.Abs(mu-mean) > 1e-6 ||
		math.Abs(norm-mat.Norm(vec, 2)) > 1e-12 || math.Abs(norm*norm-42) > 1e-12 {
		log.Fatal("Gonum mean, least-squares, or norm check failed")
	}
	PlotFirstIso(&ws, PlotPath())
	fmt.Println("Verified 12 = 3 × 4; each fiber has size 3; mean = 1.5; squared norm = 42.")
}
