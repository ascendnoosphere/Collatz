// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnExamples checks one parameter triple on a finite grid.
// The triple is multiplier 2, offset 1, and divisor 3. The grid is every
// int64 seed from -30 through 30. Exact int64 arithmetic is enough: the
// largest numerator on the grid is 2*30+1. The counts are not a proof for
// every integer.
package main

import (
	"fmt"
	"os"
	"sync"
)

const (
	exQ       int64 = 2
	exC       int64 = 1
	exD       int64 = 3
	seedMin   int64 = -30
	seedMax   int64 = 30
	exWorkers       = 4
)

// Totals records the grid checks for this one parameter triple.
type Totals struct {
	Checks        int
	Hits          int
	Traps         int
	BoundFailures int
	Failures      int
}

// Abs64 returns the absolute value of a seed or return on this grid.
func Abs64(n int64) int64 {
	if n < 0 {
		return -n
	}
	return n
}

// EuclidMod returns the remainder in {0,1,2} for a positive divisor.
// Go's % truncates toward zero, so a negative remainder is shifted by d.
func EuclidMod(n, d int64) int64 {
	r := n % d
	if r < 0 {
		r += d
	}
	return r
}

// Divides reports whether the positive divisor d divides n.
func Divides(d, n int64) bool {
	return n%d == 0
}

// FirstReturn reports the first hit for multiplier 2, offset 1, divisor 3.
// The boolean is false precisely when the Euclidean remainder is 2.
// On a hit, state is the affine value and ret is the truncating quotient.
func FirstReturn(n int64) (j, state, ret int64, ok bool) {
	switch EuclidMod(n, exD) {
	case 0:
		return 0, n, n / exD, true
	case 1:
		state = exQ*n + exC
		if !Divides(exD, state) {
			return 0, 0, 0, false
		}
		return 1, state, state / exD, true
	default:
		return 0, 0, 0, false
	}
}

// SatisfiesHitBound reports the return inequality for a hitting seed.
// A seed with no first hit returns false, so the predicate is not
// identically true.
func SatisfiesHitBound(n int64) bool {
	_, _, ret, ok := FirstReturn(n)
	if !ok {
		return false
	}
	return exD*Abs64(ret) <= exQ*Abs64(n)+exC
}

// Add folds one chunk of the grid into a running total.
func (t *Totals) Add(other Totals) {
	t.Checks += other.Checks
	t.Hits += other.Hits
	t.Traps += other.Traps
	t.BoundFailures += other.BoundFailures
	t.Failures += other.Failures
}

// InspectSeed classifies one seed and checks the return inequality.
// Each seed contributes two checks: the residue class, then either the
// bound on a hit or the rejection of the bound predicate on a trap.
func InspectSeed(n int64, tot *Totals) {
	r := EuclidMod(n, exD)
	j, state, ret, ok := FirstReturn(n)
	tot.Checks++
	switch r {
	case 0:
		tot.Hits++
		if !ok || j != 0 || state != n || ret != n/exD {
			tot.Failures++
		}
	case 1:
		tot.Hits++
		want := exQ*n + exC
		if !ok || j != 1 || state != want || ret != want/exD {
			tot.Failures++
		}
	case 2:
		tot.Traps++
		if ok {
			tot.Failures++
		}
	default:
		tot.Failures++
	}
	tot.Checks++
	if ok {
		if !SatisfiesHitBound(n) {
			tot.BoundFailures++
		}
	} else if SatisfiesHitBound(n) {
		tot.Failures++
	}
}

// SweepRange classifies every seed from lo through hi, inclusive.
func SweepRange(lo, hi int64) Totals {
	var tot Totals
	for n := lo; n <= hi; n++ {
		InspectSeed(n, &tot)
	}
	return tot
}

// RunSweep splits the seeds -30 through 30 across four chunks.
func RunSweep() Totals {
	span := int(seedMax - seedMin + 1)
	width := (span + exWorkers - 1) / exWorkers
	parts := make([]Totals, exWorkers)
	var wg sync.WaitGroup
	for w := 0; w < exWorkers; w++ {
		lo := int(seedMin) + w*width
		hi := lo + width - 1
		if lo > int(seedMax) {
			continue
		}
		if hi > int(seedMax) {
			hi = int(seedMax)
		}
		wg.Add(1)
		go func(idx, lo, hi int) {
			defer wg.Done()
			parts[idx] = SweepRange(int64(lo), int64(hi))
		}(w, lo, hi)
	}
	wg.Wait()
	var total Totals
	parts = parts[:len(parts)]
	for i := 0; i < len(parts); i++ {
		total.Add(parts[i])
	}
	return total
}

// FateTotals counts the four exclusive outcomes on the same seed grid.
type FateTotals struct {
	Seeds     int
	ToZero    int
	ToOne     int
	ToNegOne  int
	Unbounded int
	Failures  int
}

// RawStep is one raw successor for multiplier 2, offset 1, and divisor 3.
func RawStep(n int64) int64 {
	if Divides(exD, n) {
		return n / exD
	}
	return exQ*n + exC
}

// ClosedForm is the undivided value 2^k*(n+1)-1.
func ClosedForm(n int64, k uint) int64 {
	return (int64(1)<<k)*(n+1) - 1
}

// ClassifyFate returns one of "zero", "one", "neg", or "unbounded".
// The empty string reports that the bounded walk found none of the four.
func ClassifyFate(n int64) (kind string, at int64) {
	cur := n
	for step := 0; step < 64; step++ {
		switch cur {
		case 0:
			return "zero", cur
		case 1:
			return "one", cur
		case -1:
			return "neg", cur
		}
		if EuclidMod(cur, exD) == 2 {
			return "unbounded", cur
		}
		cur = RawStep(cur)
	}
	return "", n
}

// TailAgrees checks the cycle tail, or the closed form on a bad residue.
func TailAgrees(kind string, at int64) bool {
	switch kind {
	case "zero":
		return RawStep(0) == 0
	case "neg":
		return RawStep(-1) == -1
	case "one":
		return RawStep(1) == 3 && RawStep(3) == 1
	case "unbounded":
		if at == -1 || EuclidMod(at, exD) != 2 {
			return false
		}
		cur := at
		for k := uint(0); k <= 6; k++ {
			if cur != ClosedForm(at, k) || Divides(exD, cur) {
				return false
			}
			if k < 6 {
				cur = RawStep(cur)
			}
		}
		return Abs64(ClosedForm(at, 6)) > Abs64(at)
	default:
		return false
	}
}

// SweepFates classifies every seed from lo through hi, inclusive.
func SweepFates(lo, hi int64) FateTotals {
	var tot FateTotals
	for n := lo; n <= hi; n++ {
		tot.Seeds++
		kind, at := ClassifyFate(n)
		if !TailAgrees(kind, at) {
			tot.Failures++
			continue
		}
		switch kind {
		case "zero":
			tot.ToZero++
		case "one":
			tot.ToOne++
		default:
			if kind == "neg" {
				tot.ToNegOne++
			} else if kind == "unbounded" {
				tot.Unbounded++
			} else {
				tot.Failures++
			}
		}
	}
	return tot
}

// RunFates splits the fate classification across four chunks.
func RunFates() FateTotals {
	span := int(seedMax - seedMin + 1)
	width := (span + exWorkers - 1) / exWorkers
	parts := make([]FateTotals, exWorkers)
	var wg sync.WaitGroup
	for w := 0; w < exWorkers; w++ {
		lo := int(seedMin) + w*width
		hi := lo + width - 1
		if lo > int(seedMax) {
			continue
		}
		if hi > int(seedMax) {
			hi = int(seedMax)
		}
		wg.Add(1)
		go func(idx, lo, hi int) {
			defer wg.Done()
			parts[idx] = SweepFates(int64(lo), int64(hi))
		}(w, lo, hi)
	}
	wg.Wait()
	var total FateTotals
	parts = parts[:len(parts)]
	for i := 0; i < len(parts); i++ {
		total.Seeds += parts[i].Seeds
		total.ToZero += parts[i].ToZero
		total.ToOne += parts[i].ToOne
		total.ToNegOne += parts[i].ToNegOne
		total.Unbounded += parts[i].Unbounded
		total.Failures += parts[i].Failures
	}
	return total
}

// main prints the hit totals and the four fate totals.
func main() {
	total := RunSweep()
	fates := RunFates()
	fmt.Printf(
		"signed return examples: checks %d, hits %d, traps %d, "+
			"bound failures %d\n",
		total.Checks, total.Hits, total.Traps, total.BoundFailures)
	fmt.Printf(
		"fates: seeds %d, zero %d, one %d, neg %d, unbounded %d, "+
			"failures %d\n",
		fates.Seeds, fates.ToZero, fates.ToOne, fates.ToNegOne,
		fates.Unbounded, fates.Failures)
	if total.Failures != 0 || total.BoundFailures != 0 || fates.Failures != 0 {
		os.Exit(1)
	}
}
