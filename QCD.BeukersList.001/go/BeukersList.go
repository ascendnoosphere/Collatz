// Copyright (c) 2026 ascendnoosphere
// SPDX-License-Identifier: CC-BY-4.0

// Command BeukersList checks the displayed pairs x^2+D=2^n on a finite grid.
// The grid is not the unbounded statement.
package main

import (
	"fmt"
	"math/big"
	"os"
	"sync"
)

const (
	boxMaxN       = 32
	mersenneMinK  = 4
	mersenneMaxK  = 32
	workerCount   = 4
	controlChecks = 3
)

// Pair is one triple (D, x, n) in the equation x^2+D=2^n.
type Pair struct {
	D uint64
	X uint64
	N uint64
}

// Totals counts certificate steps and disagreements.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// Workspace holds reusable big-integer buffers for the seven displayed pairs.
type Workspace struct {
	Sq  *big.Int
	Pow *big.Int
	Sum *big.Int
	Acc *big.Int
}

// Cache holds the positive roots found in one exponent interval.
type Cache struct {
	Hits []Pair
}

// displayedPairs is the finite list being checked, not a completeness claim.
var displayedPairs = []Pair{
	{D: 7, X: 1, N: 3},
	{D: 7, X: 3, N: 4},
	{D: 7, X: 5, N: 5},
	{D: 7, X: 11, N: 7},
	{D: 7, X: 181, N: 15},
	{D: 23, X: 3, N: 5},
	{D: 23, X: 45, N: 11},
}

// wantSeven is the positive solution list for D=7 and n<=32.
var wantSeven = []Pair{
	{D: 7, X: 1, N: 3},
	{D: 7, X: 3, N: 4},
	{D: 7, X: 5, N: 5},
	{D: 7, X: 11, N: 7},
	{D: 7, X: 181, N: 15},
}

// wantTwenty is the positive solution list for D=23 and n<=32.
var wantTwenty = []Pair{
	{D: 23, X: 3, N: 5},
	{D: 23, X: 45, N: 11},
}

// nearMisses are positive triples that do not satisfy the equation.
var nearMisses = []Pair{
	{D: 7, X: 2, N: 3},
	{D: 7, X: 1, N: 4},
	{D: 23, X: 1, N: 5},
	{D: 23, X: 4, N: 5},
}

// Check records one certificate step.
func (t *Totals) Check(pass bool) {
	t.Checks++
	if !pass {
		t.Failures++
	}
}

// Add merges another counter.
func (t *Totals) Add(other Totals) {
	t.Checks += other.Checks
	t.Failures += other.Failures
}

// NewWorkspace prepares buffers large enough for exponents through 64.
func NewWorkspace() *Workspace {
	w := &Workspace{
		Sq:  new(big.Int),
		Pow: new(big.Int),
		Sum: new(big.Int),
		Acc: new(big.Int),
	}
	w.Pow.Lsh(big.NewInt(1), 64)
	return w
}

// NewCache preallocates room for every exponent in the box.
func NewCache() *Cache {
	return &Cache{Hits: make([]Pair, 0, boxMaxN+1)}
}

// DisplayedHolds reports whether x^2+D=2^n using the workspace buffers.
func DisplayedHolds(w *Workspace, p Pair) bool {
	w.Sq.SetUint64(p.X)
	w.Sq.Mul(w.Sq, w.Sq)
	w.Acc.SetUint64(p.D)
	w.Sum.Add(w.Sq, w.Acc)
	w.Pow.SetUint64(1)
	w.Pow.Lsh(w.Pow, uint(p.N))
	return w.Sum.Cmp(w.Pow) == 0
}

// EquationHolds is the same equation on uint64, rejecting overflow.
func EquationHolds(d, x, n uint64) bool {
	if n >= 64 {
		return false
	}
	pow := uint64(1) << n
	if x != 0 && x > pow/x {
		return false
	}
	sq := x * x
	if sq > pow {
		return false
	}
	return pow-sq == d
}

// CertificateOK requires every displayed pair and rejects every near miss.
func CertificateOK(pred func(d, x, n uint64) bool) bool {
	for _, p := range displayedPairs {
		if !pred(p.D, p.X, p.N) {
			return false
		}
	}
	for _, p := range nearMisses {
		if pred(p.D, p.X, p.N) {
			return false
		}
	}
	return true
}

// IntegerSquareRoot returns the greatest integer whose square is at most n.
func IntegerSquareRoot(n uint64) uint64 {
	if n == 0 {
		return 0
	}
	lo := uint64(1)
	hi := uint64(1) << 32
	if n < hi {
		hi = n
	}
	for lo+1 < hi {
		mid := lo + (hi-lo)/2
		if mid > n/mid {
			hi = mid
		} else {
			lo = mid
		}
	}
	return lo
}

// PositiveRoot returns s>0 with s^2=2^n-D, when that remainder is a positive square.
func PositiveRoot(d, n uint64) (uint64, bool) {
	if n >= 64 {
		return 0, false
	}
	pow := uint64(1) << n
	if pow < d {
		return 0, false
	}
	r := pow - d
	s := IntegerSquareRoot(r)
	if s == 0 || s*s != r {
		return 0, false
	}
	return s, true
}

// SweepN tests each exponent in [lo, hi] and stores positive roots.
func SweepN(d uint64, lo, hi int, cache *Cache, totals *Totals) {
	for n := lo; n <= hi; n++ {
		s, ok := PositiveRoot(d, uint64(n))
		pass := !ok || EquationHolds(d, s, uint64(n))
		totals.Check(pass)
		if ok {
			cache.Hits = append(cache.Hits, Pair{D: d, X: s, N: uint64(n)})
		}
	}
}

// SplitRange partitions the inclusive interval into contiguous blocks.
func SplitRange(lo, hi, parts int) [][2]int {
	out := make([][2]int, parts)
	span := hi - lo + 1
	base := span / parts
	rem := span % parts
	cur := lo
	for i := 0; i < parts; i++ {
		width := base
		if i < rem {
			width++
		}
		if width == 0 {
			out[i] = [2]int{1, 0}
			continue
		}
		out[i] = [2]int{cur, cur + width - 1}
		cur += width
	}
	return out
}

// SamePairs reports whether two root lists agree in order.
func SamePairs(got, want []Pair) bool {
	if len(got) != len(want) {
		return false
	}
	got = got[:len(got)]
	want = want[:len(want)]
	for i := range got {
		if got[i] != want[i] {
			return false
		}
	}
	return true
}

// RunBox sweeps n=0..boxMaxN in parallel and returns the roots in exponent order.
func RunBox(d uint64) (Totals, []Pair) {
	bounds := SplitRange(0, boxMaxN, workerCount)
	totals := make([]Totals, workerCount)
	caches := make([]*Cache, workerCount)
	var wg sync.WaitGroup
	for i, bound := range bounds {
		if bound[0] > bound[1] {
			continue
		}
		wg.Add(1)
		go func(i, lo, hi int) {
			defer wg.Done()
			caches[i] = NewCache()
			SweepN(d, lo, hi, caches[i], &totals[i])
		}(i, bound[0], bound[1])
	}
	wg.Wait()
	var merged Totals
	hits := make([]Pair, 0, 8)
	for i := range bounds {
		merged.Add(totals[i])
		if caches[i] != nil {
			hits = append(hits, caches[i].Hits...)
		}
	}
	return merged, hits
}

// SquareFits returns a^2 when it fits in uint64.
func SquareFits(a uint64) (uint64, bool) {
	if a != 0 && a > ^uint64(0)/a {
		return 0, false
	}
	return a * a, true
}

// MersenneAt checks the two representations and their distinctness at one k.
func MersenneAt(k uint, totals *Totals) {
	pow := uint64(1) << k
	totals.Check(1+(pow-1) == pow)
	root := (uint64(1) << (k - 1)) - 1
	sq, ok := SquareFits(root)
	target := uint64(1) << (2*k - 2)
	second := ok && sq <= target && target-sq == pow-1
	totals.Check(second)
	distinct := root != 1 && uint64(k) != 2*uint64(k)-2
	totals.Check(distinct)
}

// RunMersenne checks 4<=k<=32. Exponents above this box are not claimed.
func RunMersenne() Totals {
	bounds := SplitRange(mersenneMinK, mersenneMaxK, workerCount)
	totals := make([]Totals, workerCount)
	var wg sync.WaitGroup
	for i, bound := range bounds {
		if bound[0] > bound[1] {
			continue
		}
		wg.Add(1)
		go func(i, lo, hi int) {
			defer wg.Done()
			for k := lo; k <= hi; k++ {
				MersenneAt(uint(k), &totals[i])
			}
		}(i, bound[0], bound[1])
	}
	wg.Wait()
	var merged Totals
	for i := range totals {
		merged.Add(totals[i])
	}
	return merged
}

// ExpectedChecks is the number of steps in certify, not a theorem.
func ExpectedChecks() uint64 {
	displayed := uint64(len(displayedPairs))
	box := uint64(2 * (boxMaxN + 1))
	match := uint64(2)
	span := mersenneMaxK - mersenneMinK + 1
	mersenne := uint64(3 * span)
	return displayed + box + match + mersenne + controlChecks
}

// Certify combines the identities, bounded exponent sweeps, and predicate controls.
func Certify() Totals {
	var totals Totals
	work := NewWorkspace()
	for _, p := range displayedPairs {
		totals.Check(DisplayedHolds(work, p))
	}
	for _, spec := range []struct {
		d    uint64
		want []Pair
	}{
		{d: 7, want: wantSeven},
		{d: 23, want: wantTwenty},
	} {
		box, hits := RunBox(spec.d)
		totals.Add(box)
		totals.Check(SamePairs(hits, spec.want))
	}
	totals.Add(RunMersenne())
	totals.Check(CertificateOK(EquationHolds))
	always := func(uint64, uint64, uint64) bool { return true }
	never := func(uint64, uint64, uint64) bool { return false }
	totals.Check(!CertificateOK(always))
	totals.Check(!CertificateOK(never))
	return totals
}

// main prints the check count. A zero failure count is only the finite grid.
func main() {
	totals := Certify()
	fmt.Printf("dyadic square checks: %d, failures: %d\n", totals.Checks, totals.Failures)
	if totals.Failures != 0 {
		os.Exit(1)
	}
}
