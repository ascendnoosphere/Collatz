// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math/big"
	"testing"
)

// TestWarmHighOffsetAllocations checks replay buffers, including a nonunit composite phase.
func TestWarmHighOffsetAllocations(t *testing.T) {
	cases := [...]struct {
		base, u, v, a, s int
		seed             int64
	}{
		{4, 1, 3, 4, 2, 16},
		{9, 7, 8, 17, 8, 1},
		{2, 1, 3, 204, 3, 12},
		{2, 1, 2, 3, 1, -5},
	}
	for _, parameters := range cases {
		var workspace Workspace
		if err := Configure(&workspace, parameters.base, parameters.u, parameters.v,
			parameters.a, parameters.s); err != nil {
			t.Fatal(err)
		}
		workspace.seed.SetInt64(parameters.seed)
		var failure error
		allocations := testing.AllocsPerRun(20, func() {
			failure = CheckSeed(&workspace, &workspace.seed, parameters.u, parameters.v)
		})
		if failure != nil {
			t.Fatal(failure)
		}
		if allocations != 0 {
			t.Fatalf("base=%d a=%d seed=%d: warmed allocations=%g",
				parameters.base, parameters.a, parameters.seed, allocations)
		}
	}
}

// TestDivisibleOffsetResidual verifies that the source's t-free offset hypothesis is unnecessary.
func TestDivisibleOffsetResidual(t *testing.T) {
	var workspace Workspace
	if err := Configure(&workspace, 4, 1, 3, 4, 4); err != nil {
		t.Fatal(err)
	}
	for _, seed := range [...]int64{16, -16} {
		workspace.seed.SetInt64(seed)
		if err := CheckSeed(&workspace, &workspace.seed, 1, 3); err != nil {
			t.Fatal(err)
		}
	}
}

// TestHighOffsetContractRefusal separates invalid hypotheses from bounded-resource refusals.
func TestHighOffsetContractRefusal(t *testing.T) {
	cases := [...][5]int{
		{1, 1, 2, 3, 1}, {10, 1, 2, 3, 1}, {2, 0, 2, 3, 1},
		{2, 2, 2, 4, 1}, {2, 1, 9, 10, 1}, {2, 2, 4, 6, 1},
		{2, 1, 2, 2, 1}, {2, 1, 2, 257, 1}, {2, 1, 2, 3, 0},
		{2, 1, 2, 3, 9},
	}
	for _, parameters := range cases {
		var workspace Workspace
		if err := Configure(&workspace, parameters[0], parameters[1], parameters[2],
			parameters[3], parameters[4]); err == nil {
			t.Fatalf("accepted refused parameters %v", parameters)
		}
	}
	if err := Configure(nil, 2, 1, 2, 3, 1); err == nil {
		t.Fatal("accepted nil workspace")
	}
	var workspace Workspace
	seed := big.NewInt(1)
	if err := CheckSeed(&workspace, seed, 1, 2); err == nil {
		t.Fatal("accepted unconfigured workspace")
	}
	if err := Configure(&workspace, 2, 1, 2, 3, 1); err != nil {
		t.Fatal(err)
	}
	if err := CheckSeed(&workspace, nil, 1, 2); err == nil {
		t.Fatal("accepted nil seed")
	}
	if err := CheckSeed(&workspace, seed, 1, 3); err == nil {
		t.Fatal("accepted mismatched phase parameters")
	}
	seed.SetBit(seed, workspace.seedBits, 1)
	if err := CheckSeed(&workspace, seed, 1, 2); err == nil {
		t.Fatal("accepted seed exceeding reserved capacity")
	}
}

// TestHighOffsetBoundary preserves the periodic counterexample below the threshold.
func TestHighOffsetBoundary(t *testing.T) {
	if err := CheckThresholdBoundary(); err != nil {
		t.Fatal(err)
	}
}

// TestWholeBaseNotPrimeOrder distinguishes divisibility by four from its prime factor.
func TestWholeBaseNotPrimeOrder(t *testing.T) {
	var workspace Workspace
	if err := Configure(&workspace, 4, 1, 3, 4, 2); err != nil {
		t.Fatal(err)
	}
	workspace.current.SetInt64(2)
	if order := WholeOrder(&workspace); order != 0 {
		t.Fatalf("order of 2 in base 4=%d, expected 0", order)
	}
	workspace.current.SetInt64(-32)
	if order := WholeOrder(&workspace); order != 2 {
		t.Fatalf("order of -32 in base 4=%d, expected 2", order)
	}
}

// TestSignedHighOffsetReplay checks all seed/offset sign pairings and excludes zero.
func TestSignedHighOffsetReplay(t *testing.T) {
	for _, s := range [...]int{1, -1} {
		var workspace Workspace
		if err := Configure(&workspace, 2, 1, 2, 3, s); err != nil {
			t.Fatal(err)
		}
		for _, seed := range [...]int64{1, -1, 5, -5} {
			workspace.seed.SetInt64(seed)
			if err := CheckSeed(&workspace, &workspace.seed, 1, 2); err != nil {
				t.Fatalf("s=%d seed=%d: %v", s, seed, err)
			}
		}
		workspace.seed.SetInt64(0)
		if err := CheckSeed(&workspace, &workspace.seed, 1, 2); err == nil {
			t.Fatal("zero is a fixed point, not an escaping phase")
		}
	}
}
