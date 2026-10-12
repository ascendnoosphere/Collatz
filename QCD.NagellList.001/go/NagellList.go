// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command NagellList checks x^2+7 = 2^n on a finite grid.
// The grid contains the five displayed pairs and seven pairs that fail.
// The count of checks is not a classification of the positive solutions.
package main

import (
	"errors"
	"fmt"
	"math/big"
	"os"
)

// NagellPair is one pair (x, n) for the equation x^2 + 7 = 2^n.
type NagellPair struct {
	X uint64
	N uint
}

// Workspace reuses the buffers for the square, the left side, and the power.
type Workspace struct {
	X     *big.Int
	Left  *big.Int
	Pow   *big.Int
	Seven *big.Int
	One   *big.Int
}

// NewWorkspace allocates the five buffers once.
func NewWorkspace() *Workspace {
	return &Workspace{
		X:     new(big.Int),
		Left:  new(big.Int),
		Pow:   new(big.Int),
		Seven: big.NewInt(7),
		One:   big.NewInt(1),
	}
}

// DisplayedNagellPairs returns the five displayed solutions.
func DisplayedNagellPairs() []NagellPair {
	return []NagellPair{
		{X: 1, N: 3},
		{X: 3, N: 4},
		{X: 5, N: 5},
		{X: 11, N: 7},
		{X: 181, N: 15},
	}
}

// ControlNagellPairs returns pairs at which x^2 + 7 is not 2^n.
func ControlNagellPairs() []NagellPair {
	return []NagellPair{
		{X: 0, N: 3},
		{X: 2, N: 3},
		{X: 4, N: 5},
		{X: 6, N: 5},
		{X: 10, N: 7},
		{X: 181, N: 14},
		{X: 181, N: 16},
	}
}

// SatisfiesNagell reports whether x^2 + 7 equals 2^n in exact arithmetic.
func SatisfiesNagell(w *Workspace, x uint64, n uint) bool {
	w.X.SetUint64(x)
	w.Left.Mul(w.X, w.X)
	w.Left.Add(w.Left, w.Seven)
	w.Pow.Lsh(w.One, n)
	return w.Left.Cmp(w.Pow) == 0
}

// RunGrid checks the displayed pairs and the control pairs.
// The returned integer is the number of checks.
// A displayed failure or a control success is an error.
func RunGrid(w *Workspace) (int, error) {
	checks := 0
	for _, p := range DisplayedNagellPairs() {
		checks++
		if !SatisfiesNagell(w, p.X, p.N) {
			return checks, errors.New("displayed pair failed")
		}
	}
	for _, p := range ControlNagellPairs() {
		checks++
		if SatisfiesNagell(w, p.X, p.N) {
			return checks, errors.New("control pair satisfied the equation")
		}
	}
	return checks, nil
}

// main prints the number of grid checks.
func main() {
	w := NewWorkspace()
	count, err := RunGrid(w)
	if err != nil {
		fmt.Fprintln(os.Stderr, err.Error())
		os.Exit(1)
	}
	fmt.Printf("check count: %d\n", count)
}
