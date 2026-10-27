// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnMagnitude recomputes both sides of the affine triangle
// bound and of the one-seed return bound in int64. The grid keeps |q|^j
// strictly below 2^20. Agreement on this grid is not a proof for every
// integer.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the exact grid. With |q| <= 8 and j <= 6 one has
// |q|^j <= 8^6 = 262144 < 2^20. Seeds satisfy |n| <= 16 and offsets
// |c| <= 12, so |q|^j*|n| <= 4194304 and the offset term is smaller than
// 12*(8^6)/7. Both sides of each comparison fit in an int64. The six
// divisors are ±2, ±3, and ±5.
const (
	magQMin    = -8
	magQMax    = 8
	magJMax    = 6
	magNMin    = -16
	magNMax    = 16
	magCMin    = -12
	magCMax    = 12
	magBudget  = int64(1) << 20
	magWorkers = 4
)

// magnitudeDivisors is the signed divisor list used by the return sweep.
var magnitudeDivisors = [6]int64{-5, -3, -2, 2, 3, 5}

// Totals counts comparisons and disagreements of one sweep.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// Add accumulates a worker total into the receiver.
func (t *Totals) Add(other Totals) {
	t.Checks += other.Checks
	t.Failures += other.Failures
}

// Workspace holds q^j and the offset sum through the grid horizon.
// Load refills the existing buffers. A workspace is not safe for
// concurrent calls.
type Workspace struct {
	Pow  []int64
	Trap []int64
	Live bool
}

// NewWorkspace allocates the power and offset buffers once.
func NewWorkspace() *Workspace {
	return &Workspace{
		Pow:  make([]int64, magJMax+1),
		Trap: make([]int64, magJMax+1),
	}
}

// Abs64 returns the absolute value of x on the stated grid.
// The grid never contains the most negative int64.
func Abs64(x int64) int64 {
	if x < 0 {
		return -x
	}
	return x
}

// Load fills q^j and the sum of q^0 through q^(j-1) for every grid time.
// The empty power is 1 and the empty sum is 0, including q = 0.
func (w *Workspace) Load(q int64) {
	pow := int64(1)
	trap := int64(0)
	ps := w.Pow[:len(w.Pow)]
	ts := w.Trap[:len(w.Trap)]
	for j := 0; j < len(ps); j++ {
		ps[j] = pow
		ts[j] = trap
		trap += pow
		pow *= q
	}
	w.Live = true
}

// Affine returns q^j*n + c*U_j(q) from a loaded workspace.
func (w *Workspace) Affine(c, n int64, j int) int64 {
	ps := w.Pow[:len(w.Pow)]
	ts := w.Trap[:len(w.Trap)]
	return ps[j]*n + c*ts[j]
}

// TriangleLeft returns the absolute value of the affine state.
func (w *Workspace) TriangleLeft(c, n int64, j int) int64 {
	return Abs64(w.Affine(c, n, j))
}

// TriangleRight returns |q|^j*|n| + |c|*|U_j(q)|.
func (w *Workspace) TriangleRight(c, n int64, j int) int64 {
	ps := w.Pow[:len(w.Pow)]
	ts := w.Trap[:len(w.Trap)]
	return Abs64(ps[j])*Abs64(n) + Abs64(c)*Abs64(ts[j])
}

// Divides reports whether d divides a in Z. Zero divides only zero.
func Divides(d, a int64) bool {
	if d == 0 {
		return a == 0
	}
	return a%d == 0
}

// IsFirstHit reports whether j is the first time d divides the affine state.
// The workspace must already be loaded through time j.
func (w *Workspace) IsFirstHit(c, d, n int64, j int) bool {
	ps := w.Pow[:len(w.Pow)]
	ts := w.Trap[:len(w.Trap)]
	if !w.Live || j < 0 || j >= len(ps) {
		return false
	}
	if !Divides(d, ps[j]*n+c*ts[j]) {
		return false
	}
	for i := 0; i < j; i++ {
		if Divides(d, ps[i]*n+c*ts[i]) {
			return false
		}
	}
	return true
}

// AffineTriangleAt reports that the affine absolute value is at most bound,
// and that bound is exactly the triangle majorant. A larger or smaller
// claim is false. A function that always returns true does not implement it.
func (w *Workspace) AffineTriangleAt(c, n int64, j int, bound int64) bool {
	if !w.Live || j < 0 || j >= len(w.Pow) {
		return false
	}
	if bound != w.TriangleRight(c, n, j) {
		return false
	}
	return w.TriangleLeft(c, n, j) <= bound
}

// ReturnMagnitudeAt reports one first hit whose recomputed quotient magnitude
// equals left and whose triangle majorant equals right, with left <= right.
// It is false when j is not a first hit. A constant true does not implement it.
func (w *Workspace) ReturnMagnitudeAt(c, d, n int64, j int, left, right int64) bool {
	if !w.IsFirstHit(c, d, n, j) {
		return false
	}
	state := w.Affine(c, n, j)
	gotLeft := Abs64(d) * Abs64(state/d)
	gotRight := w.TriangleRight(c, n, j)
	if left != gotLeft || right != gotRight {
		return false
	}
	return left <= right
}

// QuotientMagnitude returns |d| * |A/d| for a loaded affine state.
// The division is exact when d divides A, and Go truncates toward zero.
func (w *Workspace) QuotientMagnitude(c, d, n int64, j int) int64 {
	state := w.Affine(c, n, j)
	return Abs64(d) * Abs64(state/d)
}

// SweepQ checks one multiplier. Every coefficient, seed, and time contributes
// a triangle comparison. Every divisor contributes a return comparison, which
// fails if a non-hit is accepted or a hit violates the recomputed bound.
func SweepQ(q int64, w *Workspace) Totals {
	var t Totals
	w.Load(q)
	ps := w.Pow[:len(w.Pow)]
	for j := 0; j < len(ps); j++ {
		t.Checks++
		if Abs64(ps[j]) >= magBudget {
			t.Failures++
		}
	}
	for c := int64(magCMin); c <= magCMax; c++ {
		for n := int64(magNMin); n <= magNMax; n++ {
			for j := 0; j <= magJMax; j++ {
				right := w.TriangleRight(c, n, j)
				t.Checks++
				if !w.AffineTriangleAt(c, n, j, right) {
					t.Failures++
				}
			}
		}
	}
	divs := magnitudeDivisors
	ds := divs[:]
	for di := 0; di < len(ds); di++ {
		d := ds[di]
		for c := int64(magCMin); c <= magCMax; c++ {
			for n := int64(magNMin); n <= magNMax; n++ {
				for j := 0; j <= magJMax; j++ {
					t.Checks++
					if w.IsFirstHit(c, d, n, j) {
						left := w.QuotientMagnitude(c, d, n, j)
						right := w.TriangleRight(c, n, j)
						if !w.ReturnMagnitudeAt(c, d, n, j, left, right) {
							t.Failures++
						}
					} else if w.ReturnMagnitudeAt(c, d, n, j, 0, 0) {
						t.Failures++
					}
				}
			}
		}
	}
	return t
}

// TriangleDomain counts the triangle tuples without evaluating them.
func TriangleDomain() uint64 {
	qCount := uint64(magQMax - magQMin + 1)
	cCount := uint64(magCMax - magCMin + 1)
	nCount := uint64(magNMax - magNMin + 1)
	jCount := uint64(magJMax + 1)
	return qCount * cCount * nCount * jCount
}

// ReturnDomain counts the return tuples without evaluating them.
func ReturnDomain() uint64 {
	return TriangleDomain() * uint64(len(magnitudeDivisors))
}

// BudgetDomain counts the power-budget tuples, one per multiplier and time.
func BudgetDomain() uint64 {
	qCount := uint64(magQMax - magQMin + 1)
	jCount := uint64(magJMax + 1)
	return qCount * jCount
}

// SweepDomain is the number of comparisons performed by one full sweep.
func SweepDomain() uint64 {
	return BudgetDomain() + TriangleDomain() + ReturnDomain()
}

// SweepAll splits the multiplier range across workers and sums their totals.
func SweepAll() Totals {
	count := magQMax - magQMin + 1
	qs := make([]int64, 0, count)
	for q := int64(magQMin); q <= magQMax; q++ {
		qs = append(qs, q)
	}
	parts := make([]Totals, len(qs))
	var wg sync.WaitGroup
	for worker := 0; worker < magWorkers; worker++ {
		wg.Add(1)
		go func(worker int) {
			defer wg.Done()
			w := NewWorkspace()
			for i := worker; i < len(qs); i += magWorkers {
				parts[i] = SweepQ(qs[i], w)
			}
		}(worker)
	}
	wg.Wait()
	var total Totals
	for i := 0; i < len(parts); i++ {
		total.Add(parts[i])
	}
	return total
}

// main prints the number of comparisons and exits nonzero on a disagreement.
func main() {
	total := SweepAll()
	fmt.Printf("magnitude checks: %d, failures: %d\n", total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
