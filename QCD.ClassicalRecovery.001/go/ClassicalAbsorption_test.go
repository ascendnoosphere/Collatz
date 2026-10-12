// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// TestNamedClockAndTail checks the nontrivial binary and ternary presentation simultaneously.
func TestNamedClockAndTail(t *testing.T) {
	workspace := &Workspace{}
	if err := Configure(workspace, 2, 2); err != nil {
		t.Fatal(err)
	}
	seed := big.NewInt(5)
	if err := CheckSeed(workspace, seed); err != nil {
		t.Fatal(err)
	}
	if err := CheckCycle(workspace); err != nil {
		t.Fatal(err)
	}
}

// TestRawBranchControls independently specifies signed, zero and positive one-step outputs.
func TestRawBranchControls(t *testing.T) {
	workspace := &Workspace{}
	if err := Configure(workspace, 2, 2); err != nil {
		t.Fatal(err)
	}
	controls := []struct {
		input, output int64
		affine        bool
	}{
		{5, 96, true}, {96, 48, false}, {3, 72, true}, {9, 144, true},
		{-5, -24, true}, {-24, -12, false}, {0, 0, false},
	}
	for _, control := range controls {
		workspace.raw.SetInt64(control.input)
		affine := Step(&workspace.raw, &workspace.q, &workspace.c, workspace)
		if affine != control.affine || workspace.raw.Int64() != control.output {
			t.Fatalf("input=%d: output=%s affine=%t", control.input, &workspace.raw, affine)
		}
	}
}

// TestLargeSignedSeeds exercises both signs at 501 bits with the largest admitted exponents.
func TestLargeSignedSeeds(t *testing.T) {
	workspace := &Workspace{}
	if err := Configure(workspace, MaxBinaryExponent, MaxTernaryExponent); err != nil {
		t.Fatal(err)
	}
	var seed big.Int
	seed.SetBit(&seed, 500, 1)
	seed.Add(&seed, big.NewInt(1))
	if err := CheckSeed(workspace, &seed); err != nil {
		t.Fatal(err)
	}
	seed.Neg(&seed)
	if err := CheckSeed(workspace, &seed); err != nil {
		t.Fatal(err)
	}
}

// TestRefusals preserves the prior configuration when an inadmissible resource is requested.
func TestRefusals(t *testing.T) {
	workspace := &Workspace{}
	if err := Configure(nil, 0, 0); err == nil {
		t.Fatal("nil workspace accepted")
	}
	for _, exponents := range [][2]int{{-1, 0}, {65, 0}, {0, -1}, {0, 33}} {
		if err := Configure(workspace, exponents[0], exponents[1]); err == nil {
			t.Fatalf("invalid exponents accepted: %v", exponents)
		}
	}
	seed := big.NewInt(27)
	if err := CheckSeed(workspace, seed); err == nil {
		t.Fatal("unconfigured workspace accepted")
	}
	if err := CheckCycle(nil); err == nil {
		t.Fatal("nil cycle workspace accepted")
	}
	if err := Configure(workspace, 2, 2); err != nil {
		t.Fatal(err)
	}
	if err := Configure(workspace, 65, 32); err == nil {
		t.Fatal("oversized binary exponent accepted")
	}
	if workspace.a != 2 || workspace.b != 2 {
		t.Fatal("refused configuration mutated the previous exponents")
	}
	if err := CheckSeed(nil, seed); err == nil {
		t.Fatal("nil replay workspace accepted")
	}
	if err := CheckSeed(workspace, nil); err == nil {
		t.Fatal("nil seed accepted")
	}
	seed.SetInt64(0)
	if err := CheckSeed(workspace, seed); err == nil {
		t.Fatal("zero seed accepted by the finite replay contract")
	}
	seed.SetBit(seed, MaxSeedBits, 1)
	if err := CheckSeed(workspace, seed); err == nil {
		t.Fatal("oversized seed accepted")
	}
}

// TestWarmReplayAllocations scopes the allocation claim to these four warmed presentations.
func TestWarmReplayAllocations(t *testing.T) {
	for _, exponents := range [][2]int{{0, 0}, {16, 12}, {64, 32}, {3, 0}} {
		workspace := &Workspace{}
		if err := Configure(workspace, exponents[0], exponents[1]); err != nil {
			t.Fatal(err)
		}
		seed := big.NewInt(27)
		if err := CheckSeed(workspace, seed); err != nil {
			t.Fatal(err)
		}
		var failure error
		allocations := testing.AllocsPerRun(100, func() {
			if err := CheckSeed(workspace, seed); err != nil {
				failure = err
			}
		})
		if failure != nil || allocations != 0 {
			t.Fatalf("a=%d b=%d: allocations=%g failure=%v",
				exponents[0], exponents[1], allocations, failure)
		}
	}
}

// TestPrimitivePeriods checks every finite-contract exponent pair, without extrapolation.
func TestPrimitivePeriods(t *testing.T) {
	workspace := &Workspace{}
	for a := 0; a <= MaxBinaryExponent; a++ {
		for b := 0; b <= MaxTernaryExponent; b++ {
			if err := Configure(workspace, a, b); err != nil {
				t.Fatal(err)
			}
			if err := CheckCycle(workspace); err != nil {
				t.Fatalf("a=%d b=%d: %v", a, b, err)
			}
		}
	}
}

// TestFiniteBoxCount checks the exact independent product count for the main replay domain.
func TestFiniteBoxCount(t *testing.T) {
	var total uint64
	for chunk := 0; chunk < 8; chunk++ {
		var count uint64
		var failure error
		CheckChunk(chunk, &count, &failure)
		if failure != nil {
			t.Fatalf("chunk=%d: %v", chunk, failure)
		}
		total += count
	}
	const expected = 17 * 13 * 128
	if total != expected {
		t.Fatalf("got %d certificates, want %d", total, expected)
	}
}
