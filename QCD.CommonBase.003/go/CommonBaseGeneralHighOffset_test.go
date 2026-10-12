// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// TestAllExponentOrders covers both orderings, equality, and nonunit composite residuals.
func TestAllExponentOrders(t *testing.T) {
	cases := []struct{ base, u, v, a, s, seed int }{
		{2, 2, 4, 7, 1, 1},
		{2, 2, 4, 7, 1, 4},
		{4, 2, 4, 7, 2, 32},
		{9, 4, 8, 14, -8, -1},
		{2, 2, 4, 205, 3, 12},
		{2, 2, 4, 7, 1, -5},
		{2, 3, 2, 5, 1, 1},
		{2, 2, 1, 3, -1, -1},
		{4, 2, 2, 4, 2, 2},
		{9, 8, 1, 11, -8, -1},
	}
	for _, c := range cases {
		var workspace Workspace
		if err := Configure(&workspace, c.base, c.u, c.v, c.a, c.s); err != nil {
			t.Fatal(err)
		}
		seed := big.NewInt(int64(c.seed))
		if err := CheckSeed(&workspace, seed); err != nil {
			t.Fatalf("%+v: %v", c, err)
		}
	}
}

// TestNamedRawRay checks the three-step same-map ray, not only coefficient equality.
func TestNamedRawRay(t *testing.T) {
	var workspace Workspace
	if err := Configure(&workspace, 2, 2, 4, 7, 1); err != nil {
		t.Fatal(err)
	}
	seed := big.NewInt(1)
	if err := CheckSeed(&workspace, seed); err != nil {
		t.Fatal(err)
	}
	if workspace.u+workspace.v != 3 || workspace.betas[0].Cmp(big.NewInt(40)) != 0 ||
		workspace.current.Cmp(big.NewInt(81)) != 0 {
		t.Fatal("expected return ray 1,41,81 with raw clock three and increment forty")
	}
}

// TestLargeSignedDivisionPrefix exercises exact initial divisions on a 402-bit signed seed.
func TestLargeSignedDivisionPrefix(t *testing.T) {
	for _, sign := range []int{-1, 1} {
		var workspace Workspace
		if err := Configure(&workspace, 2, 2, 4, 205, -3); err != nil {
			t.Fatal(err)
		}
		seed := big.NewInt(int64(sign * 3))
		seed.Lsh(seed, 400)
		if err := CheckSeed(&workspace, seed); err != nil {
			t.Fatal(err)
		}
	}
}

// TestRefusals separates execution limits and zero from mathematical seed coverage.
func TestRefusals(t *testing.T) {
	var workspace Workspace
	for _, c := range [][5]int{{1, 2, 4, 7, 1}, {2, 0, 4, 7, 1}, {2, 2, 4, 5, 1},
		{2, 2, 4, 257, 1}, {2, 9, 4, 14, 1}, {2, 2, 0, 3, 1}, {2, 2, 4, 7, 0}, {2, 2, 4, 7, 9}} {
		if Configure(&workspace, c[0], c[1], c[2], c[3], c[4]) == nil {
			t.Fatal("invalid or oversized parameter contract accepted")
		}
	}
	if err := CheckSeed(&workspace, big.NewInt(1)); err == nil {
		t.Fatal("unconfigured workspace accepted")
	}
	if err := Configure(&workspace, 2, 2, 4, 7, 1); err != nil {
		t.Fatal(err)
	}
	if CheckSeed(&workspace, big.NewInt(0)) == nil || CheckSeed(&workspace, nil) == nil {
		t.Fatal("zero or nil seed accepted")
	}
	var oversized big.Int
	oversized.SetBit(&oversized, MaxSeedBits, 1)
	if CheckSeed(&workspace, &oversized) == nil {
		t.Fatal("oversized seed accepted")
	}
}

// TestWarmReplayAllocations measures only replay after coefficient/storage preparation.
func TestWarmReplayAllocations(t *testing.T) {
	for _, c := range [][6]int{{2, 2, 4, 7, 1, 1}, {9, 4, 8, 14, -8, -1},
		{2, 2, 4, 205, 3, 12}, {2, 2, 4, 7, 1, -5},
		{2, 3, 2, 5, 1, 1}, {4, 2, 2, 4, 2, 2}, {9, 8, 1, 11, -8, -1}} {
		var workspace Workspace
		if err := Configure(&workspace, c[0], c[1], c[2], c[3], c[4]); err != nil {
			t.Fatal(err)
		}
		seed := big.NewInt(int64(c[5]))
		allocations := testing.AllocsPerRun(20, func() {
			if err := CheckSeed(&workspace, seed); err != nil {
				panic(err)
			}
		})
		if allocations != 0 {
			t.Fatalf("%v: warmed replay allocations=%g", c, allocations)
		}
	}
}

// TestFiniteBoxCount compares replay enumeration with independent finite-contract counting.
func TestFiniteBoxCount(t *testing.T) {
	total := 0
	for base := 2; base <= 9; base++ {
		count := 0
		var failure error
		CheckBase(base, &count, &failure)
		if failure != nil {
			t.Fatal(failure)
		}
		total += count
	}
	expected := CountFiniteContract()
	if expected != 7432128 {
		t.Fatalf("finite-contract formula=%d, expected7432128", expected)
	}
	if total != expected {
		t.Fatalf("certificate count=%d, expected%d", total, expected)
	}
}

// CountFiniteContract counts ordinary seeds and each nonzero whole-base phase residual.
func CountFiniteContract() int {
	total := 0
	for base := 2; base <= 9; base++ {
		for v := 1; v <= MaxPhaseCount; v++ {
			for u := 1; u <= MaxPhaseCount; u++ {
				g := Gcd(u, v)
				rebased := 1
				for i := 0; i < g; i++ {
					rebased *= base
				}
				phaseResiduals := 16 - 2*(8/rebased)
				total += 3 * 16 * (256 + (v/g)*phaseResiduals)
			}
		}
	}
	return total
}

// TestMultipleForcedDivisions checks a phase that requires two consecutive raw divisions.
func TestMultipleForcedDivisions(t *testing.T) {
	var workspace Workspace
	if err := Configure(&workspace, 2, 3, 2, 5, 1); err != nil {
		t.Fatal(err)
	}
	workspace.current.SetInt64(1)
	states := [...]int64{40, 10, 112, 28, 7}
	for i, expected := range states {
		ApplyRawStep(&workspace)
		if workspace.current.Cmp(big.NewInt(expected)) != 0 {
			t.Fatalf("step%d expected%d got%s", i+1, expected, &workspace.current)
		}
	}
	if workspace.betas[0].Cmp(big.NewInt(6)) != 0 {
		t.Fatal("expected increment six and raw clock five")
	}
}

// TestAdditiveCompressedCase checks exponent equality and the physical non-additive raw map.
func TestAdditiveCompressedCase(t *testing.T) {
	var workspace Workspace
	if err := Configure(&workspace, 2, 2, 2, 4, 1); err != nil {
		t.Fatal(err)
	}
	if err := CheckSeed(&workspace, big.NewInt(1)); err != nil {
		t.Fatal(err)
	}
	if workspace.u != 1 || workspace.v != 1 ||
		workspace.betas[0].Cmp(big.NewInt(4)) != 0 ||
		workspace.current.Cmp(big.NewInt(9)) != 0 {
		t.Fatal("expected original raw ray 1,5,9 with clock two and increment four")
	}
}

// TestSignAlignmentCounterexample rejects extending the intermediate bound before alignment.
func TestSignAlignmentCounterexample(t *testing.T) {
	var workspace Workspace
	if err := Configure(&workspace, 2, 3, 2, 12, 1); err != nil {
		t.Fatal(err)
	}
	workspace.current.SetInt64(-767)
	for i := 0; i < 5; i++ {
		ApplyRawStep(&workspace)
	}
	if workspace.current.Cmp(big.NewInt(1)) != 0 ||
		workspace.betas[0].Cmp(big.NewInt(768)) != 0 {
		t.Fatal("expected misaligned ray -767 to1 in five raw steps")
	}
	if err := CheckSeed(&workspace, big.NewInt(-767)); err != nil {
		t.Fatal(err)
	}
}
