// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// TestNoncoprimePresentations covers carried residuals and composite nonunit phases.
func TestNoncoprimePresentations(t *testing.T) {
	cases := []struct{ base, u, v, a, s, seed int }{
		{2, 2, 4, 7, 1, 1},
		{2, 2, 4, 7, 1, 4},
		{4, 2, 4, 7, 2, 32},
		{9, 4, 8, 14, -8, -1},
		{2, 2, 4, 205, 3, 12},
		{2, 2, 4, 7, 1, -5},
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
		if workspace.gcd <= 1 {
			t.Fatal("noncoprime exponent case was not retained")
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
		{2, 2, 4, 257, 1}, {2, 2, 4, 7, 0}, {2, 2, 4, 7, 9}} {
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
		{2, 2, 4, 205, 3, 12}, {2, 2, 4, 7, 1, -5}} {
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

// TestFiniteBoxCount checks the explicit noncoprime sample contract, not all parameters.
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
	if total != 807744 {
		t.Fatalf("certificate count=%d, expected807744", total)
	}
}
