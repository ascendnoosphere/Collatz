// SPDX-License-Identifier: CC-BY-4.0
package main

import "testing"

// ConfigureWorkspace sets one small signed map and its common-power expansion.
func ConfigureWorkspace(workspace *Workspace, d, q, c int64, a int) {
	power := int64(1)
	for i := 0; i < a; i++ {
		power *= d
	}
	workspace.d.SetInt64(d)
	workspace.q.SetInt64(q)
	workspace.c.SetInt64(c)
	workspace.Q.SetInt64(power * q)
	workspace.C.SetInt64(power * c)
}

// TestNegativeDivisorPrimitiveExpansion checks sign-changing division and clock correction.
func TestNegativeDivisorPrimitiveExpansion(t *testing.T) {
	var workspace Workspace
	InitializeWorkspace(&workspace)
	ConfigureWorkspace(&workspace, -2, -1, -1, 1)
	found, err := CheckSeed(&workspace, 1, 1)
	if !found || err != nil {
		t.Fatalf("compressed cycle: found=%t error=%v", found, err)
	}
	if workspace.states[1].Int64() != -2 || workspace.states[2].Int64() != 1 {
		t.Fatal("compressed period should be two with one affine instruction")
	}
	workspace.current.SetInt64(1)
	for _, expected := range [...]int64{4, -2, 1} {
		ApplyRawStep(&workspace, &workspace.Q, &workspace.C,
			&workspace.current, &workspace.next)
		workspace.current.Set(&workspace.next)
		if workspace.current.Int64() != expected {
			t.Fatalf("raw phase=%s expected=%d", &workspace.current, expected)
		}
	}
}

// TestInteriorRawSeedPhaseSelection prevents a false same-seed periodicity implication.
func TestInteriorRawSeedPhaseSelection(t *testing.T) {
	var workspace Workspace
	InitializeWorkspace(&workspace)
	ConfigureWorkspace(&workspace, 2, 1, 1, 2)
	found, err := CheckSeed(&workspace, 8, 2)
	if !found || err != nil {
		t.Fatalf("cycle-phase search: found=%t error=%v", found, err)
	}
	for i, expected := range [...]int64{8, 4, 2, 1, 2} {
		if workspace.states[i].Int64() != expected {
			t.Fatalf("compressed phase %d=%s expected=%d", i, &workspace.states[i], expected)
		}
	}
	workspace.current.SetInt64(8)
	for i, expected := range [...]int64{4, 2, 1, 8} {
		ApplyRawStep(&workspace, &workspace.Q, &workspace.C,
			&workspace.current, &workspace.next)
		workspace.current.Set(&workspace.next)
		if workspace.current.Int64() != expected {
			t.Fatalf("raw phase %d=%s expected=%d", i+1, &workspace.current, expected)
		}
	}
}

// TestZeroPrimitiveReturn preserves division precedence when the affine offset is nonzero.
func TestZeroPrimitiveReturn(t *testing.T) {
	var workspace Workspace
	InitializeWorkspace(&workspace)
	ConfigureWorkspace(&workspace, -5, 3, -3, 3)
	found, err := CheckSeed(&workspace, 0, 3)
	if !found || err != nil || workspace.states[1].Sign() != 0 {
		t.Fatalf("zero fixed point: found=%t error=%v", found, err)
	}
}

// TestNoRepeatRemainsUndecided checks that a capped search returns no cycle certificate.
func TestNoRepeatRemainsUndecided(t *testing.T) {
	var workspace Workspace
	InitializeWorkspace(&workspace)
	ConfigureWorkspace(&workspace, 2, 1, 2, 0)
	found, err := CheckSeed(&workspace, 1, 0)
	if found || err != nil {
		t.Fatalf("capped nonrepeat search: found=%t error=%v", found, err)
	}
}

// TestInvalidPeriodIndices rejects empty clocks and inputs outside the bounded contract.
func TestInvalidPeriodIndices(t *testing.T) {
	var workspace Workspace
	InitializeWorkspace(&workspace)
	for _, indices := range [...][3]int{
		{-1, 1, 0}, {0, 0, 0}, {0, SampleBudget + 1, 0}, {0, 1, -1}, {0, 1, 4},
	} {
		if CheckExpandedPeriod(&workspace, indices[0], indices[1], indices[2]) == nil {
			t.Fatalf("accepted invalid indices %v", indices)
		}
	}
}

// TestFiniteGridAndAllocations measures the warmed loop over the entire stated finite grid.
func TestFiniteGridAndAllocations(t *testing.T) {
	var workspace Workspace
	InitializeWorkspace(&workspace)
	cases, cycles := 0, 0
	var failure error
	allocations := testing.AllocsPerRun(1, func() {
		cases, cycles = 0, 0
		failure = CheckPeriodRange(&workspace, -30, 31, &cases, &cycles)
	})
	if failure != nil || cases != 95648 || cycles != 58864 {
		t.Fatalf("finite grid: cases=%d cycles=%d error=%v", cases, cycles, failure)
	}
	if allocations != 0 {
		t.Fatalf("warmed finite-grid allocations=%g, expected zero", allocations)
	}
	t.Logf("finite seeds=%d expansion certificates=%d hot-loop allocations=%g",
		cases, cycles, allocations)
}
