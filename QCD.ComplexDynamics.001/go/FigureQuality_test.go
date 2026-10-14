// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"bytes"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"gonum.org/v1/plot/vg"
	"gonum.org/v1/plot/vg/draw"
	"gonum.org/v1/plot/vg/vgsvg"
)

// TestHomogeneousAxis checks the new all-seed theorem without treating a zero transverse
// coordinate as an injective observable.
func TestHomogeneousAxis(t *testing.T) {
	f := ScalarFamilies()[2]
	if !ProvenScalarEscape(f, Point{1, 0}) || ProvenScalarEscape(f, Point{}) {
		t.Fatal("homogeneous axis or zero boundary failed")
	}
	w := Workspace{Seen: make(map[Point]int, Ticks+1)}
	if got := Diagnose(f, Point{1, 0}, &w); got.Class != "proved homogeneous escape" {
		t.Fatalf("incorrect axis diagnosis: %+v", got)
	}
	for _, seed := range []int64{-2, -1, 1, 2} {
		z := Point{seed, 0}
		seen := make(map[int64]bool, 16)
		for j := 0; j < 16 && Inside(z); j++ {
			magnitude := max(z.Re, -z.Re)
			if seen[magnitude] {
				t.Fatal("independent homogeneous axis magnitude repeated")
			}
			seen[magnitude] = true
			z, _ = RawStep(f, z)
		}
	}
}

// TestFiniteEdgePairs checks all masks and ensures every changing edge is used once.
func TestFiniteEdgePairs(t *testing.T) {
	for code := 0; code < 16; code++ {
		var mask [4]bool
		want := 0
		for j := range mask {
			mask[j] = code&(1<<j) != 0
		}
		for j := range mask {
			if mask[j] != mask[(j+1)%4] {
				want++
			}
		}
		edges, count := EdgePairs(mask)
		if count != want || count%2 != 0 {
			t.Fatalf("invalid crossing count for mask %d", code)
		}
		var seen [4]bool
		for j := 0; j < count; j++ {
			edge := edges[j]
			if seen[edge] || mask[edge] == mask[(edge+1)%4] {
				t.Fatalf("invalid paired edge for mask %d", code)
			}
			seen[edge] = true
		}
	}
}

// TestFiniteHorizon checks deterministic escape times and the unchanged shared-point law.
func TestFiniteHorizon(t *testing.T) {
	p := Polynomial{Name: "constant", Coefficients: []float64{0},
		MinX: -2, MaxX: 2, MinY: -2, MaxY: 2}
	if EscapeLevel(p, 9, 128) != 0 || EscapeLevel(p, 1, 128) != 129 {
		t.Fatal("finite-horizon boundary was changed")
	}
	levels := make([]int, Mesh*Mesh)
	for j := range levels {
		levels[j] = JuliaTicks + 1
	}
	check := CompareHorizons(p, levels)
	if check.Samples != 65536 || check.EarlierSurvivors != check.Samples ||
		check.LaterSurvivors != check.Samples || check.NewlyEscaped != 0 {
		t.Fatalf("incorrect shared-grid law: %+v", check)
	}
}

// TestRasterSelection verifies explicit output selection despite Plot's recording canvas.
func TestRasterSelection(t *testing.T) {
	p := NewPlot("Tile check", "$\\operatorname{Re}z$", "$\\operatorname{Im}z$")
	p.X.Min, p.X.Max, p.Y.Min, p.Y.Max = -1, 1, -1, 1
	panel := JuliaPanel{Polynomial: Polynomial{MinX: -1, MaxX: 1, MinY: -1, MaxY: 1},
		Levels: make([]int, Mesh*Mesh)}
	p.Add(&panel)
	for _, raster := range []bool{false, true} {
		panel.Raster = raster
		canvas := vgsvg.New(vg.Inch, vg.Inch)
		p.Draw(draw.New(canvas))
		var buffer bytes.Buffer
		if _, err := canvas.WriteTo(&buffer); err != nil {
			t.Fatal(err)
		}
		if got := strings.Contains(buffer.String(), "<image"); got != raster {
			t.Fatalf("incorrect image selection: raster=%v image=%v", raster, got)
		}
	}
}

// TestSVGContainsNoRaster checks the publication format and outlined text directly.
func TestSVGContainsNoRaster(t *testing.T) {
	p := NewPlot("Vector check", "$\\operatorname{Re}z$", "$\\operatorname{Im}z$")
	p.X.Min, p.X.Max, p.Y.Min, p.Y.Max = -1, 1, -1, 1
	p.Add(LegendPanel{[]LegendEntry{{"sampled edge", ClassColor(Result{})}}})
	path := filepath.Join(t.TempDir(), "Figure.svg")
	SaveSVG(p, path)
	data, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	body := string(data)
	if !strings.Contains(body, "<svg") || !strings.Contains(body, "<path") ||
		strings.Contains(body, "<image") || strings.Contains(body, "<text") {
		t.Fatal("SVG does not consist of vector geometry and outlined glyphs")
	}
}
