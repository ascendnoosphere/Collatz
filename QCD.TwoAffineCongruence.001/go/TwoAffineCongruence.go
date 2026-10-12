// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command TwoAffineCongruence checks the two-affine congruence on a finite grid.
// The grid contains five integral lanes, five failed congruences, and one even partner.
// The count of checks is not the classification of the quotients.
package main

import (
	"errors"
	"fmt"
	"os"
)

// Lane is one exponent pair and one integer coefficient.
type Lane struct {
	K int64
	Q int64
	A int64
}

// Witness is a lane whose two quotients are the integers N and Y.
type Witness struct {
	Lane Lane
	N    int64
	Y    int64
}

// Cache stores the powers of two used by every lane.
type Cache struct {
	Pow []int64
}

// Workspace reuses the power table.
type Workspace struct {
	Cache Cache
}

// NewWorkspace allocates powers 2^0 through 2^16 once.
func NewWorkspace() *Workspace {
	pow := make([]int64, 17)
	pow[0] = 1
	for i := 1; i < len(pow); i++ {
		pow[i] = pow[i-1] * 2
	}
	return &Workspace{Cache: Cache{Pow: pow}}
}

// Pow2 returns 2^a from the cache.
func (w *Workspace) Pow2(a int64) (int64, bool) {
	if a < 0 || int(a) >= len(w.Cache.Pow) {
		return 0, false
	}
	pow := w.Cache.Pow[:len(w.Cache.Pow)]
	return pow[a], true
}

// Delta returns 2^K - q^2.
func (w *Workspace) Delta(k, q int64) (int64, bool) {
	pow, ok := w.Pow2(k)
	if !ok {
		return 0, false
	}
	return pow - q*q, true
}

// PositiveLanes returns the five integral lanes with odd positive denominator.
func PositiveLanes() []Witness {
	return []Witness{
		{Lane: Lane{K: 4, Q: 3, A: 2}, N: 1, Y: 1},
		{Lane: Lane{K: 5, Q: 5, A: 1}, N: 1, Y: 3},
		{Lane: Lane{K: 5, Q: 5, A: 4}, N: 3, Y: 1},
		{Lane: Lane{K: 2, Q: 1, A: 1}, N: 1, Y: 1},
		{Lane: Lane{K: 6, Q: 7, A: 3}, N: 1, Y: 1},
	}
}

// ControlLanes returns lanes whose first numerator is not divisible by Delta.
func ControlLanes() []Lane {
	return []Lane{
		{K: 4, Q: 3, A: 1},
		{K: 5, Q: 5, A: 2},
		{K: 3, Q: 1, A: 1},
		{K: 4, Q: 3, A: 0},
		{K: 6, Q: 7, A: 1},
	}
}

// BoundaryLane returns the lane K=1, q=1, a=1, whose partner quotient is 2.
func BoundaryLane() Witness {
	return Witness{Lane: Lane{K: 1, Q: 1, A: 1}, N: 3, Y: 2}
}

// Divides reports whether delta divides num, with delta nonzero.
func Divides(delta, num int64) bool {
	if delta == 0 {
		return false
	}
	return num%delta == 0
}

// Congruent reports whether 2^a + q is divisible by delta.
func (w *Workspace) Congruent(delta, q, a int64) bool {
	pow, ok := w.Pow2(a)
	if !ok {
		return false
	}
	return Divides(delta, pow+q)
}

// Odd reports whether z is an odd integer.
func Odd(z int64) bool {
	return z%2 != 0
}

// CheckPositive checks one integral lane, including the unit seed and the odd length.
func (w *Workspace) CheckPositive(item Witness) error {
	lane := item.Lane
	delta, ok := w.Delta(lane.K, lane.Q)
	if !ok || delta <= 0 || !Odd(delta) || lane.A >= lane.K {
		return errors.New("positive lane lost its odd positive denominator")
	}
	powA, okA := w.Pow2(lane.A)
	powB, okB := w.Pow2(lane.K - lane.A)
	if !okA || !okB {
		return errors.New("positive exponent left the power table")
	}
	numN := lane.Q + powA
	numY := lane.Q + powB
	if !Divides(delta, numN) || !w.Congruent(delta, lane.Q, lane.A) {
		return errors.New("positive lane failed the congruence")
	}
	if item.N*delta != numN || item.Y*delta != numY {
		return errors.New("positive quotients disagree with the numerators")
	}
	if !Odd(item.Y) {
		return errors.New("positive partner is even")
	}
	if lane.Q*item.N+1 != powA*item.Y {
		return errors.New("first product identity failed")
	}
	if lane.Q*item.Y+1 != powB*item.N {
		return errors.New("second product identity failed")
	}
	if item.N == item.Y {
		if lane.Q != powA-1 || lane.K != 2*lane.A || item.N != 1 {
			return errors.New("equal quotients are not the unit seed")
		}
	}
	if Odd(lane.K) && item.N == item.Y {
		return errors.New("odd length had equal quotients")
	}
	return nil
}

// CheckControl checks that a failed lane is neither integral nor congruent.
func (w *Workspace) CheckControl(lane Lane) error {
	delta, ok := w.Delta(lane.K, lane.Q)
	if !ok || delta <= 0 {
		return errors.New("control denominator is not positive")
	}
	powA, okA := w.Pow2(lane.A)
	if !okA {
		return errors.New("control exponent left the power table")
	}
	if Divides(delta, lane.Q+powA) || w.Congruent(delta, lane.Q, lane.A) {
		return errors.New("control lane satisfied the congruence")
	}
	return nil
}

// CheckBoundary checks the even partner at exponent zero.
func (w *Workspace) CheckBoundary(item Witness) error {
	lane := item.Lane
	delta, ok := w.Delta(lane.K, lane.Q)
	if !ok || delta <= 0 || lane.A != lane.K {
		return errors.New("boundary lane is not the zero-exponent case")
	}
	powA, okA := w.Pow2(lane.A)
	powB, okB := w.Pow2(lane.K - lane.A)
	if !okA || !okB {
		return errors.New("boundary exponent left the power table")
	}
	if item.N*delta != lane.Q+powA || item.Y*delta != lane.Q+powB {
		return errors.New("boundary quotients disagree with the numerators")
	}
	if !w.Congruent(delta, lane.Q, lane.A) {
		return errors.New("boundary lane failed the congruence")
	}
	if Odd(item.Y) {
		return errors.New("boundary partner was odd")
	}
	return nil
}

// RunGrid checks every positive lane, every control, and the boundary lane.
// The returned integer is the number of checks.
func (w *Workspace) RunGrid() (int, error) {
	checks := 0
	for _, item := range PositiveLanes() {
		checks++
		if err := w.CheckPositive(item); err != nil {
			return checks, err
		}
	}
	for _, lane := range ControlLanes() {
		checks++
		if err := w.CheckControl(lane); err != nil {
			return checks, err
		}
	}
	checks++
	if err := w.CheckBoundary(BoundaryLane()); err != nil {
		return checks, err
	}
	return checks, nil
}

// main prints the number of grid checks.
func main() {
	w := NewWorkspace()
	count, err := w.RunGrid()
	if err != nil {
		fmt.Fprintln(os.Stderr, err.Error())
		os.Exit(1)
	}
	fmt.Printf("check count: %d\n", count)
}
