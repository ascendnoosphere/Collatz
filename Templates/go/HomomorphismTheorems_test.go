package main

import (
	"math"
	"os"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"testing"

	stdfnt "golang.org/x/image/font"
	"golang.org/x/image/math/fixed"
	"gonum.org/v1/plot"
	"gonum.org/v1/plot/font"
)

// ExpectPanic checks invalid-input contracts without allowing silent acceptance.
func ExpectPanic(t *testing.T, action func()) {
	t.Helper()
	// Recover only within this helper so a missing panic fails the calling test.
	defer func() {
		if recover() == nil {
			t.Error("expected invalid input to panic")
		}
	}()
	action()
}

// TestApplyModHom checks canonical residues, chunk boundaries, and supported aliasing.
func TestApplyModHom(t *testing.T) {
	previous := runtime.GOMAXPROCS(0)
	defer runtime.GOMAXPROCS(previous)
	domain := []int{-9, -4, -1, 0, 1, 4, 8, 11}
	want := []int{3, 0, 3, 0, 1, 0, 0, 3}
	for _, workers := range []int{1, 2, 64} {
		runtime.GOMAXPROCS(workers)
		values := make([]int, len(domain)+1)
		values[len(domain)] = 99
		ApplyModHom(values, domain, 4)
		if !reflect.DeepEqual(values[:len(domain)], want) || values[len(domain)] != 99 {
			t.Fatalf("workers=%d: incorrect output %v", workers, values)
		}
		inPlace := append([]int(nil), domain...)
		ApplyModHom(inPlace, inPlace, 4)
		if !reflect.DeepEqual(inPlace, want) {
			t.Fatalf("workers=%d: incorrect in-place output %v", workers, inPlace)
		}
	}
	ApplyModHom(nil, nil, 4)
	// Both zero moduli and undersized outputs are invalid even before workers start.
	ExpectPanic(t, func() { ApplyModHom(nil, nil, 0) })
	ExpectPanic(t, func() { ApplyModHom(nil, []int{1}, 4) })
}

// TestCacheReuse checks exact fibers and stale-state removal when buffers are reused.
func TestCacheReuse(t *testing.T) {
	domain := make([]int, 12)
	values := make([]int, 12)
	for i := range domain {
		domain[i] = i
	}
	ApplyModHom(values, domain, 4)
	var cache Cache
	cache.KernelFill(domain, values, 0)
	cache.ImageFill(values, 4)
	cache.FiberSizes(values, 4)
	if !reflect.DeepEqual(cache.Kernel, []int{0, 4, 8}) ||
		!reflect.DeepEqual(cache.Image, []int{0, 1, 2, 3}) ||
		!reflect.DeepEqual(cache.fibers, []float64{3, 3, 3, 3}) ||
		!FirstIsoCardinalities(&cache, 12) {
		t.Fatalf("incorrect cyclic-group data: %+v", cache)
	}
	kernel, image, fibers := &cache.Kernel[:cap(cache.Kernel)][0],
		&cache.Image[:cap(cache.Image)][0], &cache.fibers[0]
	scratch := cache.AsFloat(values)
	firstScratch := &scratch[0]
	ApplyModHom(values, domain, 2)
	cache.KernelFill(domain, values, 0)
	cache.ImageFill(values, 2)
	cache.FiberSizes(values, 2)
	if !reflect.DeepEqual(cache.Kernel, []int{0, 2, 4, 6, 8, 10}) ||
		!reflect.DeepEqual(cache.Image, []int{0, 1}) ||
		!reflect.DeepEqual(cache.fibers, []float64{6, 6}) ||
		!FirstIsoCardinalities(&cache, 12) {
		t.Fatalf("stale cache state: %+v", cache)
	}
	if kernel != &cache.Kernel[0] || image != &cache.Image[0] ||
		fibers != &cache.fibers[0] || firstScratch != &cache.AsFloat(values)[0] {
		t.Fatal("reusable buffers were replaced despite sufficient capacity")
	}
	if FirstIsoCardinalities(&cache, 0) || FirstIsoCardinalities(&cache, 11) ||
		FirstIsoCardinalities(&Cache{}, 12) {
		t.Fatal("invalid cardinality identity accepted")
	}
	cache.KernelFill(domain[:0], values[:0], 0)
	cache.ImageFill(nil, 2)
	cache.FiberSizes(nil, 2)
	if len(cache.Kernel) != 0 || len(cache.Image) != 0 ||
		!reflect.DeepEqual(cache.fibers, []float64{0, 0}) {
		t.Fatal("empty input retained old observations")
	}
	// Invalid residue data must not be dropped silently by either cache method.
	ExpectPanic(t, func() { cache.ImageFill([]int{-1}, 4) })
	ExpectPanic(t, func() { cache.ImageFill(nil, 0) })
	ExpectPanic(t, func() { cache.FiberSizes([]int{4}, 4) })
	ExpectPanic(t, func() { cache.FiberSizes(nil, 0) })
}

// TestFitConstant compares the numerical minimizer against independently known means.
func TestFitConstant(t *testing.T) {
	cases := []struct {
		Data []float64
		Mean float64
	}{
		{[]float64{0, 1, 2, 3}, 1.5},
		{[]float64{-5, -3, 2}, -2},
		{[]float64{7, 7, 7}, 7},
	}
	for _, test := range cases {
		if got := FitConstant(test.Data); math.Abs(got-test.Mean) > 1e-6 {
			t.Errorf("mean of %v: got %.9g, want %.9g", test.Data, got, test.Mean)
		}
	}
	// A least-squares mean requires finite, nonempty input.
	ExpectPanic(t, func() { FitConstant(nil) })
	ExpectPanic(t, func() { FitConstant([]float64{math.NaN()}) })
	ExpectPanic(t, func() { FitConstant([]float64{math.Inf(1)}) })
}

// TestMathLabels checks every needed glyph and the layout metrics used for alignment.
func TestMathLabels(t *testing.T) {
	p := plot.New()
	RegisterLatinModern(p)
	h := p.TextHandler.(MathLabels)
	labels := []string{
		`$|G|/|\ker\varphi|=|\operatorname{im}\varphi|$`,
		`$g\in\mathbb{Z}/12\mathbb{Z}$`,
		`$\varphi(g)\in\mathbb{Z}/4\mathbb{Z}$`,
	}
	for _, label := range labels {
		unicode, isMath := LabelText(label)
		if !isMath {
			t.Fatalf("math expression not recognized: %s", label)
		}
		fnt := LabelFont(label, font.Font{Variant: "Serif", Size: 14})
		face := h.Fonts.Lookup(fnt, fnt.Size)
		for _, r := range unicode {
			glyph, err := face.Face.GlyphIndex(nil, r)
			if err != nil || glyph == 0 {
				t.Fatalf("missing math glyph %q: %v", r, err)
			}
			ppem := fixed.Int26_6(math.Round(float64(fnt.Size) * 64))
			bounds, _, err := face.Face.GlyphBounds(nil, glyph, ppem, stdfnt.HintingNone)
			if err != nil {
				t.Fatal(err)
			}
			ext := h.Extents(fnt)
			// Nominal font metrics previously clipped the mathematical italic g.
			if -float64(bounds.Min.Y)/64 > float64(ext.Ascent) ||
				float64(bounds.Max.Y)/64 > float64(ext.Descent) {
				t.Fatalf("math glyph %q escapes the measured label bounds", r)
			}
		}
		width, height, depth := h.Box(label, fnt)
		ext := h.Extents(fnt)
		if width <= 0 || height != ext.Ascent || depth != ext.Descent ||
			ext.Height != ext.Ascent+ext.Descent {
			t.Fatal("inconsistent single-line label metrics")
		}
	}
	if got, isMath := LabelText("12"); got != "12" || isMath {
		t.Fatal("plain tick label altered")
	}
	// Unknown expressions and multiple lines need a real renderer, not ASCII fallback.
	ExpectPanic(t, func() { LabelText("$x$") })
	ExpectPanic(t, func() { LabelText("line\nbreak") })
}

// TestPlotFirstIso executes outline rendering and verifies the requested vector PDF size.
func TestPlotFirstIso(t *testing.T) {
	ws := Workspace{Domain: make([]int, 12), Values: make([]int, 12)}
	for i := range ws.Domain {
		ws.Domain[i] = i
	}
	ApplyModHom(ws.Values, ws.Domain, 4)
	out := filepath.Join(t.TempDir(), "FirstIsoFibers.pdf")
	PlotFirstIso(&ws, out)
	data, err := os.ReadFile(out)
	if err != nil {
		t.Fatal(err)
	}
	box := regexp.MustCompile(`/MediaBox\s*\[0(?:\.0+)? 0(?:\.0+)? 432(?:\.0+)? 288(?:\.0+)?\]`)
	if len(data) < 5 || string(data[:5]) != "%PDF-" || !box.Match(data) {
		t.Fatal("output is not a 6in×4in PDF")
	}
	if filepath.Base(PlotPath()) != "FirstIsoFibers.pdf" {
		t.Fatal("unexpected template output filename")
	}
	// A specific title and axis pair must never be applied to unrelated observations.
	ExpectPanic(t, func() { PlotFirstIso(nil, out) })
	ws.Values[0] = 1
	ExpectPanic(t, func() { PlotFirstIso(&ws, out) })
}
