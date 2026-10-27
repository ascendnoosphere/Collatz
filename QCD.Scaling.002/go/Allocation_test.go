//go:build !race

// SPDX-License-Identifier: CC-BY-4.0
// Allocation budgets apply to uninstrumented builds. Under -race, sync.Pool
// randomly discards entries used by math/big, invalidating zero-allocation counts.

package main

import (
	"math/big"
	"testing"
)

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
