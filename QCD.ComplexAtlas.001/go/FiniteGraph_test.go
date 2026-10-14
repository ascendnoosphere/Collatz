// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math"
	"math/big"
	"slices"
	"testing"
)

// TestSignedMatrixRank covers noncanonical residues without an unbounded inverse search.
func TestSignedMatrixRank(t *testing.T) {
	for _, p := range []int{2, 3, 5} {
		if MatrixRank([][]int{{-1}}, p) != 1 {
			t.Fatal("negative unit did not have rank one")
		}
		if MatrixRank([][]int{{math.MaxInt, 1}, {math.MaxInt, 1}}, p) != 1 {
			t.Fatal("large equal rows did not have rank one")
		}
		if MatrixRank([][]int{{-p, p}, {0, 0}}, p) != 0 {
			t.Fatal("multiples of the characteristic were nonzero")
		}
		if MatrixRank(nil, p) != 0 || MatrixRank([][]int{{}, {}}, p) != 0 {
			t.Fatal("empty matrix did not have rank zero")
		}
	}
}

// TestRaggedMatrix rejects shapes outside the elimination contract explicitly.
func TestRaggedMatrix(t *testing.T) {
	defer func() {
		if got := recover(); got != "cochain matrix must be rectangular" {
			t.Fatalf("wrong ragged-matrix rejection: %v", got)
		}
	}()
	MatrixRank([][]int{{1, 0}, {1}}, 3)
}

// TestPrimeExponentBoundary excludes the zero-input and unit-divisor infinite loops.
func TestPrimeExponentBoundary(t *testing.T) {
	for _, input := range [][2]int64{{0, 2}, {1, 1}, {-1, 2}} {
		t.Run("rejected", func(t *testing.T) {
			defer func() {
				if got := recover(); got != "prime exponent requires n >= 1 and p >= 2" {
					t.Fatalf("wrong exponent rejection: %v", got)
				}
			}()
			PrimeExponent(input[0], input[1])
		})
	}
}

// TestFiniteCycleCounts preserves the four exact finite-ring cycle decompositions.
func TestFiniteCycleCounts(t *testing.T) {
	cases := []struct {
		model   Model
		modulus int
		periods []int
	}{
		{Model{"Gaussian", 0, 1}, 2, []int{4}},
		{Model{"Gaussian", 0, 1}, 3, []int{1, 4, 4}},
		{Model{"Eisenstein", -1, 1}, 2, []int{1, 3}},
		{Model{"Eisenstein", -1, 1}, 3, []int{3, 3, 3}},
	}
	for _, test := range cases {
		result := FiniteAffine(test.model, test.modulus, "regression")
		if !slices.Equal(result.CycleLengths, test.periods) {
			t.Fatalf("%s mod %d: got %v, want %v", test.model.Name, test.modulus,
				result.CycleLengths, test.periods)
		}
	}
}

// TestRawParameterRejection prevents large coefficients or invalid models from wrapping silently.
func TestRawParameterRejection(t *testing.T) {
	base := Families()[0]
	cases := []struct {
		family Family
		state  Point
	}{
		{base, Point{RawInputLimit + 1, 1}},
		{base, Point{math.MinInt64, 1}},
	}
	for _, q := range []Point{{math.MaxInt64, 0}, {0, -CoeffLimit - 1}} {
		f := base
		f.Q = q
		cases = append(cases, struct {
			family Family
			state  Point
		}{f, Point{3, 1}})
	}
	for _, test := range cases {
		t.Run("rejected", func(t *testing.T) {
			defer func() {
				if got := recover(); got !=
					"raw tick outside supported ring, parameter or coordinate bounds" {
					t.Fatalf("wrong raw-tick rejection: %v", got)
				}
			}()
			RawStep(test.family, test.state)
		})
	}
	for _, model := range []Model{{"invalid", 0, math.MaxInt64}, {"invalid", 1, 1}} {
		base.Ring = model
		if SupportedFamily(base) {
			t.Fatal("accepted an unsupported multiplication table")
		}
	}
}

// TestRawArithmeticBoundary compares worst-case signed affine ticks with arbitrary precision.
func TestRawArithmeticBoundary(t *testing.T) {
	for _, m := range []Model{{"Gaussian", 0, 1}, {"Eisenstein", -1, 1}} {
		for _, x := range []int64{-RawInputLimit + 1, RawInputLimit - 1} {
			for _, y := range []int64{-RawInputLimit + 1, RawInputLimit - 1} {
				f := Family{"boundary", m, Point{CoeffLimit, -CoeffLimit},
					Point{-CoeffLimit, CoeffLimit}, Point{2, 0}, "raw"}
				got, divides := RawStep(f, Point{x, y})
				if divides {
					t.Fatal("odd boundary input unexpectedly divided")
				}
				// These independent products do not narrow until the exact final sum is checked.
				a := new(big.Int).Mul(big.NewInt(f.Q.Re), big.NewInt(x))
				b := new(big.Int).Mul(big.NewInt(f.Q.Im), big.NewInt(y))
				a.Sub(a, b).Add(a, big.NewInt(f.C.Re))
				c := new(big.Int).Mul(big.NewInt(f.Q.Re), big.NewInt(y))
				e := new(big.Int).Mul(big.NewInt(f.Q.Im), big.NewInt(x))
				c.Add(c, e)
				b.Mul(b, big.NewInt(m.Tau))
				c.Add(c, b).Add(c, big.NewInt(f.C.Im))
				if !a.IsInt64() || !c.IsInt64() || got != (Point{a.Int64(), c.Int64()}) {
					t.Fatal("bounded signed raw tick disagreed with exact arithmetic")
				}
			}
		}
	}
}

// BenchmarkFiniteAffine measures the complete fixed census, including all three matrix ranks.
func BenchmarkFiniteAffine(b *testing.B) {
	for _, model := range []Model{{"Gaussian", 0, 1}, {"Eisenstein", -1, 1}} {
		for _, modulus := range []int{2, 3} {
			name := model.Name + string(rune('0'+modulus))
			b.Run(name, func(b *testing.B) {
				b.ReportAllocs()
				for i := 0; i < b.N; i++ {
					FiniteAffine(model, modulus, name)
				}
			})
		}
	}
}
