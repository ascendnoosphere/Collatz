// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"testing"
)

// TestRawCycle checks parity marks, closure and distinctness against literal integer successors.
func TestRawCycle(t *testing.T) {
	states := States()
	for j, z := range states {
		if AffineEdge(j) != (z%2 != 0) {
			t.Fatalf("edge %d has an incorrect affine mark", j)
		}
		next := z / 2
		if z%2 != 0 {
			next = 3*z - 1
		}
		if next != states[(j+1)%Edges] {
			t.Fatalf("raw edge %d does not close", j)
		}
		for k := 0; k < j; k++ {
			if z == states[k] {
				t.Fatalf("state %d repeats state %d", j, k)
			}
		}
	}
}

// TestScalarResonance contrasts the same common potential with a nonexact unit-edge cochain.
func TestScalarResonance(t *testing.T) {
	for _, p := range [2]int64{ControlPrime, ResonancePrime} {
		r := InspectCycle(p)
		neutral := ScalarPower(3, 7, p) == ScalarPower(2, 11, p)
		dimension := 0
		if neutral {
			dimension = 1
		}
		if (r.Holonomy == 1) != neutral || r.H1Dimension != dimension ||
			!r.ActualExact || r.OffsetPeriod != Residue((1-r.Holonomy)*17, p) ||
			r.UnitPeriod != 1 {
			t.Fatalf("coefficient field %d: %+v", p, r)
		}
	}
}

// TestRankControls prevents the cyclic-matrix test from accepting a constant rank answer.
func TestRankControls(t *testing.T) {
	for _, p := range [2]int64{ControlPrime, ResonancePrime} {
		var w Workspace
		if got := MatrixRank(&w, p); got != 0 {
			t.Fatalf("zero rank %d", got)
		}
		for j := 0; j < Edges; j++ {
			w.Matrix[j][j] = 1
		}
		if got := MatrixRank(&w, p); got != Edges {
			t.Fatalf("identity rank %d", got)
		}
		w.Matrix[Edges-1] = [Edges]int64{}
		if got := MatrixRank(&w, p); got != Edges-1 {
			t.Fatalf("one missing pivot rank %d", got)
		}
	}
}

// TestGaussianField exhausts the 139 base roots and all 19,321 extension elements.
func TestGaussianField(t *testing.T) {
	for r := int64(0); r < ResonancePrime; r++ {
		if (r*r+1)%ResonancePrime == 0 {
			t.Fatalf("base root %d destroys the claimed field", r)
		}
	}
	census, err := RunFieldCensus()
	if err != nil {
		t.Fatal(err)
	}
	want := FieldCensus{ResonancePrime, 19321, 19321, 139, 2, 19320, 19321}
	if census != want {
		t.Fatalf("field census %+v != %+v", census, want)
	}
}

// TestSemilinearity exhibits the nonfixed scalar and independently checks multiplication.
func TestSemilinearity(t *testing.T) {
	i := Coefficient{0, 1}
	one := Coefficient{1, 0}
	if Conjugate(GaussianMultiply(i, one)) == GaussianMultiply(i, Conjugate(one)) {
		t.Fatal("nontrivial Frobenius was incorrectly extension-field linear")
	}
	for a := int64(0); a < ResonancePrime; a++ {
		z := Coefficient{a, 1}
		for _, r := range [2]Coefficient{{a, 0}, i} {
			if Conjugate(GaussianMultiply(r, z)) !=
				GaussianMultiply(Conjugate(r), Conjugate(z)) {
				t.Fatalf("semilinearity failed at %v, %v", r, z)
			}
		}
	}
}

// TestBoundedCharacteristics rejects silent expansion to degenerate coefficient characteristics.
func TestBoundedCharacteristics(t *testing.T) {
	for _, p := range [3]int64{2, 3, 141} {
		func() {
			defer func() {
				if recover() == nil {
					t.Fatalf("unsupported characteristic %d was accepted", p)
				}
			}()
			var w Workspace
			Initialize(&w, p)
		}()
	}
}

// TestWorkspaceAllocation checks that coefficient initialization and elimination reuse buffers.
func TestWorkspaceAllocation(t *testing.T) {
	var w Workspace
	allocations := testing.AllocsPerRun(20, func() {
		Initialize(&w, ResonancePrime)
		MatrixRank(&w, ResonancePrime)
	})
	if allocations != 0 {
		t.Fatalf("hot matrix work allocates %g times per run", allocations)
	}
}

// TestFigureWord verifies every displayed prefix identity with exact binary rational arithmetic.
func TestFigureWord(t *testing.T) {
	states := States()
	factor, offset := float64(1), float64(0)
	for j := 0; j <= Edges; j++ {
		if factor*17+offset != float64(states[j%Edges]) {
			t.Fatalf("picture prefix %d loses the actual raw state", j)
		}
		if j < Edges {
			if AffineEdge(j) {
				factor, offset = 3*factor, 3*offset-1
			} else {
				factor, offset = factor/2, offset/2
			}
		}
	}
	if factor != float64(2187)/2048 || -offset/17 != float64(139)/2048 {
		t.Fatal("picture endpoint loses the exact multiplier or offset correction")
	}
}

// TestFigureLabels checks the finite label contract, explicit sizes and actual font metrics.
func TestFigureLabels(t *testing.T) {
	p := NewPlot("Font audit", "$u$", "$v$")
	if p.Title.TextStyle.Font.Size != 16 || p.X.Label.TextStyle.Font.Size != 14 ||
		p.Y.Label.TextStyle.Font.Size != 14 || p.X.Tick.Label.Font.Size != 12 ||
		p.Y.Tick.Label.Font.Size != 12 || p.Legend.TextStyle.Font.Size != 12 {
		t.Fatal("figure font sizes differ from the documented contract")
	}
	for _, label := range [8]string{
		"$u$", "$v$", "$j$", "$\\log(r)/\\log(2)$", "$-B/17$",
		"$N(z)=0$", "$N(z)=69$", "$N(z)=138$",
	} {
		if _, mathLabel := LabelText(label); !mathLabel {
			t.Fatalf("documented label %s was not recognized", label)
		}
		width, ascent, descent := p.TextHandler.Box(label, p.X.Label.TextStyle.Font)
		if width <= 0 || ascent <= 0 || descent < 0 {
			t.Fatalf("invalid actual outline metrics for %s", label)
		}
	}
	for _, bad := range [2]string{"$x$", "$u$\n"} {
		func() {
			defer func() {
				if recover() == nil {
					t.Fatalf("unsupported label %q was silently accepted", bad)
				}
			}()
			LabelText(bad)
		}()
	}
}

// TestNormPalette checks every bounded color and rejects ambiguous representative expansion.
func TestNormPalette(t *testing.T) {
	for n := int64(0); n < ResonancePrime; n++ {
		if NormColor(n).A != 255 {
			t.Fatalf("norm %d is not opaque", n)
		}
	}
	for _, bad := range [2]int64{-1, ResonancePrime} {
		func() {
			defer func() {
				if recover() == nil {
					t.Fatalf("invalid norm representative %d was accepted", bad)
				}
			}()
			NormColor(bad)
		}()
	}
}
