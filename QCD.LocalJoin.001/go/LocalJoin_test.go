// SPDX-License-Identifier: CC-BY-4.0

package main

import (
	"math"
	"testing"
)

// TestCoefficients checks every legal branch and every nonshared cross pair.
func TestCoefficients(t *testing.T) {
	if err := CheckCoefficients(); err != nil {
		t.Fatal(err)
	}
	if CoefficientStep(AffineForm{16733, 1594323}, AffineForm{50200, 4782969}) {
		t.Fatal("an odd slope was accepted as a parameter-independent continuation")
	}
}

// TestCylinder checks the full default range and the largest supported parameter.
func TestCylinder(t *testing.T) {
	var w Workspace
	for parameter := uint64(0); parameter <= 10000; parameter++ {
		if err := w.VerifyCylinder(parameter); err != nil {
			t.Fatalf("t=%d: %v", parameter, err)
		}
	}
	if err := w.VerifyCylinder(MaxParameter); err != nil {
		t.Fatal(err)
	}
	if err := w.VerifyCylinder(MaxParameter + 1); err == nil {
		t.Fatal("unsupported parameter accepted")
	}
}

// TestRawStep exercises both branches and the first overflowing odd affine input.
func TestRawStep(t *testing.T) {
	for _, pair := range [][2]uint64{{0, 0}, {1, 4}, {2, 1}, {3, 10}} {
		got, ok := RawStep(pair[0])
		if !ok || got != pair[1] {
			t.Fatalf("RawStep(%d) = %d, %v", pair[0], got, ok)
		}
	}
	if _, ok := RawStep(math.MaxUint64); ok {
		t.Fatal("overflowing affine input accepted")
	}
}

// TestWorkspaceAllocations ensures successful numerical checks reuse their buffers.
func TestWorkspaceAllocations(t *testing.T) {
	var w Workspace
	if err := w.VerifyCylinder(10000); err != nil {
		t.Fatal(err)
	}
	if allocations := testing.AllocsPerRun(100, func() {
		if err := w.VerifyCylinder(10000); err != nil {
			panic(err)
		}
	}); allocations != 0 {
		t.Fatalf("verification allocated %g objects", allocations)
	}
}
