// SPDX-License-Identifier: CC-BY-4.0

package main

import (
	"errors"
	"testing"
)

// alwaysTrue ignores the arithmetic and reports success at every positive cell.
func alwaysTrue(q, K uint64, w *Workspace) (bool, error) {
	if w == nil || q == 0 || K == 0 {
		return false, errors.New("cell is missing")
	}
	return true, nil
}

// TestConstantPredicateRejected fails a predicate with no false cell.
func TestConstantPredicateRejected(t *testing.T) {
	var w Workspace
	_, err := AuditGrid(alwaysTrue, &w)
	if err == nil {
		t.Fatal("constant true predicate was accepted")
	}
}

// TestAuditWindowCount checks the stated grid without treating it as the theorem.
func TestAuditWindowCount(t *testing.T) {
	if CountChecks() != 1840 {
		t.Fatalf("stated check count = %d, want 1840", CountChecks())
	}
	var w Workspace
	n, err := AuditWindow(&w)
	if err != nil {
		t.Fatal(err)
	}
	if n != 1840 {
		t.Fatalf("performed checks = %d, want 1840", n)
	}
}

// TestClearedComparison checks signs and floors on the odd window.
func TestClearedComparison(t *testing.T) {
	var w Workspace
	type row struct {
		q        uint64
		K        uint64
		positive bool
	}
	rows := []row{
		{1, 3, false},
		{5, 5, false},
		{11, 7, true},
		{21, 9, false},
		{45, 11, true},
		{89, 13, false},
		{181, 15, true},
		{361, 17, false},
		{723, 19, false},
		{1447, 21, false},
	}
	for _, row := range rows {
		got, err := Decide(row.q, row.K, &w)
		if err != nil {
			t.Fatalf("q=%d K=%d: %v", row.q, row.K, err)
		}
		if got != row.positive {
			t.Fatalf("q=%d K=%d: got %v, want %v", row.q, row.K, got, row.positive)
		}
	}
	type floor struct {
		K    uint64
		root uint64
		even bool
		q    uint64
	}
	floors := []floor{
		{3, 2, true, 1},
		{5, 5, false, 5},
		{7, 11, false, 11},
		{9, 22, true, 21},
		{11, 45, false, 45},
		{13, 90, true, 89},
		{15, 181, false, 181},
		{17, 362, true, 361},
		{19, 724, true, 723},
		{21, 1448, true, 1447},
	}
	for _, row := range floors {
		root, err := FloorOf(row.K, &w)
		if err != nil {
			t.Fatal(err)
		}
		if root != row.root {
			t.Fatalf("K=%d: floor %d, want %d", row.K, root, row.root)
		}
		q, even, err := OddCandidate(root)
		if err != nil {
			t.Fatal(err)
		}
		if even != row.even || q != row.q {
			t.Fatalf("K=%d: candidate (%d,%v), want (%d,%v)", row.K, q, even, row.q, row.even)
		}
	}
	if _, err := Decide(2, 3, &w); err == nil {
		t.Fatal("even q was accepted")
	}
	match, err := SquaresMatch(181, &w)
	if err != nil {
		t.Fatal(err)
	}
	if !match {
		t.Fatal("expanded square disagreed at q=181")
	}
}
