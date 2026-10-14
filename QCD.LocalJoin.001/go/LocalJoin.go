// SPDX-License-Identifier: CC-BY-4.0

package main

import (
	"fmt"
	"math"
	"os"
)

// MaxParameter is the numerical verifier's explicit input budget.
const MaxParameter uint64 = 1000000

// AffineForm retains the constant and parameter coefficient separately.
type AffineForm struct {
	Constant uint64
	Slope    uint64
}

// SourceForms includes the initial source and all 33 certified raw successors.
var SourceForms = [...]AffineForm{
	{11003, 1048576},
	{33010, 3145728},
	{16505, 1572864},
	{49516, 4718592},
	{24758, 2359296},
	{12379, 1179648},
	{37138, 3538944},
	{18569, 1769472},
	{55708, 5308416},
	{27854, 2654208},
	{13927, 1327104},
	{41782, 3981312},
	{20891, 1990656},
	{62674, 5971968},
	{31337, 2985984},
	{94012, 8957952},
	{47006, 4478976},
	{23503, 2239488},
	{70510, 6718464},
	{35255, 3359232},
	{105766, 10077696},
	{52883, 5038848},
	{158650, 15116544},
	{79325, 7558272},
	{237976, 22674816},
	{118988, 11337408},
	{59494, 5668704},
	{29747, 2834352},
	{89242, 8503056},
	{44621, 4251528},
	{133864, 12754584},
	{66932, 6377292},
	{33466, 3188646},
	{16733, 1594323},
}

// ParentForms includes the smaller parent and all seven certified raw successors.
var ParentForms = [...]AffineForm{
	{9915, 944784},
	{29746, 2834352},
	{14873, 1417176},
	{44620, 4251528},
	{22310, 2125764},
	{11155, 1062882},
	{33466, 3188646},
	{16733, 1594323},
}

// Workspace reuses both numerical prefix buffers.
type Workspace struct {
	source [34]uint64
	parent [8]uint64
}

// RawStep checks affine overflow before evaluating the raw classical map.
func RawStep(n uint64) (uint64, bool) {
	if n%2 == 0 {
		return n / 2, true
	}
	if n > (math.MaxUint64-1)/3 {
		return 0, false
	}
	return 3*n + 1, true
}

// CoefficientStep recognizes a parameter-independent legal coefficient transition.
func CoefficientStep(x, y AffineForm) bool {
	if x.Slope%2 != 0 {
		return false
	}
	if x.Constant%2 == 0 {
		return y.Constant == x.Constant/2 && y.Slope == x.Slope/2
	}
	return x.Constant <= (math.MaxUint64-1)/3 && x.Slope <= math.MaxUint64/3 &&
		y.Constant == 3*x.Constant+1 && y.Slope == 3*x.Slope
}

// Dominates certifies strict separation for every nonnegative parameter.
func Dominates(x, y AffineForm) bool {
	return x.Constant > y.Constant && x.Slope >= y.Slope
}

// CheckCoefficients checks transitions, the shared rows, and all other cross pairs.
func CheckCoefficients() error {
	source, parent := SourceForms[:], ParentForms[:]
	foreign := [...]AffineForm{{8251, 786432}, {24754, 2359296}}
	for _, forms := range [][]AffineForm{source, parent} {
		for i := 1; i < len(forms); i++ {
			if !CoefficientStep(forms[i-1], forms[i]) {
				return fmt.Errorf("illegal coefficient transition at index %d", i)
			}
		}
		for _, form := range forms {
			for _, excluded := range foreign {
				if !Dominates(form, excluded) && !Dominates(excluded, form) {
					return fmt.Errorf("coefficient exclusion fails for %+v", form)
				}
			}
		}
	}
	for i, x := range source {
		for k, y := range parent {
			shared := (i == 32 && k == 6) || (i == 33 && k == 7)
			if shared {
				if x != y {
					return fmt.Errorf("shared coefficient rows differ")
				}
			} else if !Dominates(x, y) && !Dominates(y, x) {
				return fmt.Errorf("unseparated coefficient rows %d and %d", i, k)
			}
		}
	}
	return nil
}

// VerifyCylinder compares every affine row with actual raw iterates within its budget.
func (w *Workspace) VerifyCylinder(t uint64) error {
	if t > MaxParameter {
		return fmt.Errorf("parameter exceeds supported maximum %d", MaxParameter)
	}
	source, parent := w.source[:], w.parent[:]
	// At t <= 10^6 all displayed values are below 2.3*10^13.
	for i, form := range SourceForms {
		source[i] = form.Constant + form.Slope*t
	}
	for i, form := range ParentForms {
		parent[i] = form.Constant + form.Slope*t
	}
	for _, values := range [][]uint64{source, parent} {
		for i := 1; i < len(values); i++ {
			next, ok := RawStep(values[i-1])
			if !ok || next != values[i] {
				return fmt.Errorf("raw prefix fails at index %d", i)
			}
		}
		for _, value := range values {
			if value == 8251+786432*t || value == 24754+2359296*t {
				return fmt.Errorf("excluded affine form occurs in a prefix")
			}
		}
	}
	if parent[0] == 0 || 100*parent[0] > 91*source[0] ||
		source[0] >= source[33] || source[33]%2 != (t+1)%2 {
		return fmt.Errorf("parent bound or terminal parity fails")
	}
	for i, x := range source {
		for k, y := range parent {
			shared := (i == 32 && k == 6) || (i == 33 && k == 7)
			if (x == y) != shared {
				return fmt.Errorf("unexpected prefix intersection at %d and %d", i, k)
			}
		}
	}
	return nil
}

// main checks the finite coefficient certificate and 10001 numerical parameters.
func main() {
	if err := CheckCoefficients(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	var w Workspace
	for t := uint64(0); t <= 10000; t++ {
		if err := w.VerifyCylinder(t); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	}
	fmt.Println("Checked all coefficient transitions, cross comparisons and exclusions.")
	fmt.Println("Checked exact raw prefixes and parent bounds for t = 0,...,10000.")
}
