// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import "testing"

// TestGrid requires the finite rectangle to satisfy the integer identities.
func TestGrid(t *testing.T) {
	n, ok := CheckGrid()
	if !ok {
		t.Fatal("finite grid failed")
	}
	if n <= 0 {
		t.Fatalf("check count %d", n)
	}
}

// TestExampleSeventyFive checks the seed 75, the exit 85, and the parent 64.
func TestExampleSeventyFive(t *testing.T) {
	if Pow(2, 2)*19-1 != 75 {
		t.Fatal("seed")
	}
	if (Pow(3, 2)*19-1)/2 != 85 {
		t.Fatal("exit")
	}
	if (3*85+1)/4 != 64 || 64 >= 75 {
		t.Fatal("quarter parent")
	}
}

// TestSignPredicateAccepted accepts the coefficient sign itself.
func TestSignPredicateAccepted(t *testing.T) {
	sign := func(a int64) bool { return TwoCoeff(a) > 0 }
	if !AcceptsPositiveTwo(sign) {
		t.Fatal("sign predicate rejected")
	}
}

// TestConstantTrueRejected rejects a predicate that ignores the order.
func TestConstantTrueRejected(t *testing.T) {
	constant := func(a int64) bool { return true }
	if AcceptsPositiveTwo(constant) {
		t.Fatal("constant true predicate accepted")
	}
}
