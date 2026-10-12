// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// Number constructs cold fixture coefficients, never values inside replay loops.
func Number(value int64) *big.Int {
	return big.NewInt(value)
}

// TestProperFactor exercises the obstruction to using the entire offset as the entry target.
func TestProperFactor(t *testing.T) {
	var workspace Workspace
	if err := Configure(&workspace, Number(11), Number(55), Number(2), nil); err != nil {
		t.Fatal(err)
	}
	if workspace.sigma.Int64() != 11 || workspace.coreOffset.Int64() != 5 ||
		workspace.steps != 1 {
		t.Fatal("incorrect proper-factor certificate")
	}
	if err := CheckSeed(&workspace, Number(1)); err != nil {
		t.Fatal(err)
	}
	if err := CheckSeed(&workspace, Number(-501)); err != nil {
		t.Fatal(err)
	}
}

// TestSuppliedFactor keeps generic absorption independent of the stronger gcd(C,D) hypothesis.
func TestSuppliedFactor(t *testing.T) {
	var workspace Workspace
	if Configure(&workspace, Number(3), Number(6), Number(2), nil) == nil {
		t.Fatal("automatic mode silently discarded its full-offset coprimality hypothesis")
	}
	if err := Configure(&workspace, Number(3), Number(6), Number(2), Number(3)); err != nil {
		t.Fatal(err)
	}
	if workspace.sigma.Int64() != 3 || workspace.coreOffset.Int64() != 2 {
		t.Fatal("incorrect supplied-factor reconstruction")
	}
	for n := int64(-64); n <= 64; n++ {
		if err := CheckSeed(&workspace, Number(n)); err != nil {
			t.Fatal(err)
		}
	}
}

// TestSignedAndZeroMultiplier checks signed exact divisions and the nonzero-offset q=0 branch.
func TestSignedAndZeroMultiplier(t *testing.T) {
	for _, q := range []int64{-3, 0, 3} {
		for _, c := range []int64{-45, 45} {
			for _, d := range []int64{-2, 2} {
				var workspace Workspace
				if err := Configure(&workspace, Number(q), Number(c), Number(d), nil); err != nil {
					t.Fatal(err)
				}
				for _, n := range []int64{-128, -27, -1, 0, 1, 27, 128} {
					if err := CheckSeed(&workspace, Number(n)); err != nil {
						t.Fatal(err)
					}
				}
			}
		}
	}
}

// TestNamedRawCycles checks the two prescribed odd-return cycles at every raw clock.
func TestNamedRawCycles(t *testing.T) {
	var offset big.Int
	offset.Exp(Number(181), Number(20), nil)
	var workspace Workspace
	if err := Configure(&workspace, Number(181), &offset, Number(2), nil); err != nil {
		t.Fatal(err)
	}
	if workspace.sigma.Cmp(&offset) != 0 || workspace.coreOffset.Int64() != 1 ||
		workspace.steps != 20 {
		t.Fatal("large-offset extraction failed")
	}
	for _, n := range []int64{27, 35} {
		if err := CheckCycle(&workspace, Number(n), 17); err != nil {
			t.Fatal(err)
		}
		var expected, minimum big.Int
		expected.Mul(&offset, Number(n))
		if workspace.minimum.Cmp(&expected) != 0 {
			t.Fatal("raw cycle minimum failed to scale")
		}
		minimum.Set(&expected)
		if err := SearchCutoff(&workspace, &minimum); err != nil {
			t.Fatal(err)
		}
		if workspace.cutoff.Int64() != n {
			t.Fatal("exact scaled starting cutoff changed")
		}
		minimum.Add(&minimum, Number(1))
		if err := SearchCutoff(&workspace, &minimum); err != nil {
			t.Fatal(err)
		}
		if workspace.cutoff.Int64() != n+1 {
			t.Fatal("starting cutoff was rounded down")
		}
	}
	if err := CheckCycle(&workspace, Number(27), 34); err == nil {
		t.Fatal("nonprimitive double return was accepted")
	}
}

// TestLargeSignedSeeds probes retained buffers after a long supplied power witness.
func TestLargeSignedSeeds(t *testing.T) {
	var offset, seed big.Int
	offset.Exp(Number(181), Number(20), nil)
	seed.Lsh(Number(1), 501)
	seed.Add(&seed, Number(3))
	for _, d := range []int64{-2, 2} {
		var workspace Workspace
		if err := Configure(&workspace, Number(181), &offset, Number(d), nil); err != nil {
			t.Fatal(err)
		}
		for _, sign := range []int64{-1, 1} {
			var signed big.Int
			signed.Mul(&seed, Number(sign))
			if err := CheckSeed(&workspace, &signed); err != nil {
				t.Fatal(err)
			}
		}
	}
}

// TestRefusals checks finite limits, unsupported factors and preservation of a valid tuple.
func TestRefusals(t *testing.T) {
	var workspace Workspace
	if err := CheckSeed(&workspace, Number(1)); err == nil {
		t.Fatal("unconfigured replay was accepted")
	}
	if err := Configure(&workspace, Number(11), Number(55), Number(2), nil); err != nil {
		t.Fatal(err)
	}
	cases := [][4]*big.Int{
		{nil, Number(55), Number(2), nil},
		{Number(182), Number(55), Number(2), nil},
		{Number(11), Number(0), Number(2), nil},
		{Number(11), Number(55), Number(1), nil},
		{Number(11), Number(55), Number(2), Number(0)},
		{Number(11), Number(55), Number(2), Number(7)},
		{Number(11), Number(55), Number(2), Number(5)},
		{Number(2), Number(2), Number(2), Number(2)},
	}
	for _, values := range cases {
		if Configure(&workspace, values[0], values[1], values[2], values[3]) == nil {
			t.Fatal("invalid configuration was accepted")
		}
		if workspace.q.Int64() != 11 || workspace.sigma.Int64() != 11 ||
			workspace.coreOffset.Int64() != 5 {
			t.Fatal("refusal mutated the validated tuple")
		}
	}
	var oversized big.Int
	oversized.Lsh(Number(1), MaxSeedBits)
	if CheckSeed(&workspace, &oversized) == nil || CheckSeed(&workspace, nil) == nil {
		t.Fatal("invalid seed was accepted")
	}
	if SearchCutoff(&workspace, Number(-1)) == nil {
		t.Fatal("negative natural cutoff was accepted")
	}
	if err := SearchCutoff(&workspace, Number(0)); err != nil || workspace.cutoff.Sign() != 0 {
		t.Fatal("zero ceiling cutoff failed")
	}
}

// TestWarmReplayAllocations measures only four warmed configurations with seed 27.
func TestWarmReplayAllocations(t *testing.T) {
	var offset big.Int
	offset.Exp(Number(181), Number(20), nil)
	cases := [][4]*big.Int{
		{Number(11), Number(55), Number(2), nil},
		{Number(3), Number(6), Number(2), Number(3)},
		{Number(-3), Number(45), Number(-2), nil},
		{Number(181), &offset, Number(2), nil},
	}
	for _, values := range cases {
		var workspace Workspace
		if err := Configure(&workspace, values[0], values[1], values[2], values[3]); err != nil {
			t.Fatal(err)
		}
		seed := Number(27)
		if err := CheckSeed(&workspace, seed); err != nil {
			t.Fatal(err)
		}
		var failure error
		allocations := testing.AllocsPerRun(100, func() {
			failure = CheckSeed(&workspace, seed)
		})
		if failure != nil || allocations != 0 {
			t.Fatalf("warmed replay: error=%v allocations=%g", failure, allocations)
		}
	}
}

// TestFiniteBoxCount fixes multiplicities without interpreting the box as infinite coverage.
func TestFiniteBoxCount(t *testing.T) {
	var total uint64
	for chunk := 0; chunk < 8; chunk++ {
		var count uint64
		var failure error
		CheckChunk(chunk, &count, &failure)
		if failure != nil {
			t.Fatal(failure)
		}
		total += count
	}
	if total != 1044900 {
		t.Fatalf("finite certificate count=%d, expected 1044900", total)
	}
}
