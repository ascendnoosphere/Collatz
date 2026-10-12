// SPDX-License-Identifier: CC-BY-4.0
//
// Exact certificate for QCD.Relations.Cycles.001. The program walks the
// explicit slices of the positive raw map with exact integer arithmetic and
// reports the number of checks and the number of failures. States that leave
// the machine range use math/big, so no orbit is observed through a wrapped
// word; the small sweeps run in uint64 and document their ranges.

package main

import (
	"fmt"
	"math/big"
	"os"
	"sync"
)

// Bounds of the sweeps. They are the ranges printed by the program and
// reproduced by the tests.
const (
	// cycleSliceMaxH bounds the exponent h of the slice q = 2c+1, d = 2 with
	// c = 3 (8^h - 1) / 7.
	cycleSliceMaxH = 30
	// fullAccessMaxD and fullAccessMaxK bound the slice
	// q = (d-1) d^(k-1) + 1, c = (d-1) (d^(k-1) - 1).
	fullAccessMaxD = 40
	fullAccessMaxK = 12
	// intersectionMaxD bounds the slice q = d+1, c = d-1; the check runs over
	// seeds 1..intersectionSeeds and times 0..intersectionMaxK.
	intersectionMaxD  = 40
	intersectionSeeds = 599
	intersectionMaxK  = 24
	// evenOffsetMaxC bounds the even offsets of the d = 2 slice; each seed is
	// walked until odd and then over evenOffsetGrowth further steps.
	evenOffsetMaxC   = 20
	evenOffsetSeeds  = 2000
	evenOffsetReach  = 64
	evenOffsetGrowth = 64
	// oddOffsetMaxC bounds the odd offsets of the d = 2 slice and the seeds of
	// the gcd invariance check; oddOffsetCaptureSteps bounds the walk of the
	// seed c itself, which must avoid 1.
	oddOffsetMaxC         = 41
	oddOffsetSeeds        = 2000
	oddOffsetCaptureSteps = 64
)

// Package-level constants avoid allocation inside the sweeps. They are never
// mutated.
var (
	BigOne   = big.NewInt(1)
	BigThree = big.NewInt(3)
	BigSeven = big.NewInt(7)
)

// SliceTotals counts the checks and failures of one slice.
type SliceTotals struct {
	Checks   uint64
	Failures uint64
}

// Workspace holds the buffers reused by the walks so that no walk allocates a
// new *big.Int; a buffer may still grow internally when a value widens. The
// parameter buffers Divisor, Mult and Offset are set once per case and only
// read by StepBig; the remaining buffers are scratch whose roles are documented
// where they are used.
type Workspace struct {
	Divisor *big.Int
	Mult    *big.Int
	Offset  *big.Int
	Rem     *big.Int
	Cur     *big.Int
	Next    *big.Int
	E       *big.Int
	G       *big.Int
	T0      *big.Int
	T1      *big.Int
	T2      *big.Int
	T3      *big.Int
	Exp     *big.Int
}

// NewWorkspace allocates every buffer once, already carrying a word so the
// first arithmetic operation in a walk does not allocate.
func NewWorkspace() *Workspace {
	w := &Workspace{
		Divisor: new(big.Int), Mult: new(big.Int), Offset: new(big.Int),
		Rem: new(big.Int), Cur: new(big.Int), Next: new(big.Int),
		E: new(big.Int), G: new(big.Int),
		T0: new(big.Int), T1: new(big.Int), T2: new(big.Int), T3: new(big.Int),
		Exp: new(big.Int),
	}
	for _, b := range []*big.Int{w.Divisor, w.Mult, w.Offset, w.Rem, w.Cur,
		w.Next, w.E, w.G, w.T0, w.T1, w.T2, w.T3, w.Exp} {
		b.SetUint64(1)
	}
	return w
}

// SetParams loads the raw map parameters into the workspace and returns the
// workspace for chaining.
func (w *Workspace) SetParams(d, q, c uint64) *Workspace {
	w.Divisor.SetUint64(d)
	w.Mult.SetUint64(q)
	w.Offset.SetUint64(c)
	return w
}

// Pow writes base^exp into the scratch buffer E and returns it. The exponent
// is passed through the Exp buffer, so E is the only result buffer written.
func (w *Workspace) Pow(base, exp uint64) *big.Int {
	w.Exp.SetUint64(exp)
	return w.E.SetUint64(base).Exp(w.E, w.Exp, nil)
}

// StepBig applies one instruction of the raw map at the state held in cur and
// writes the result into next; it returns next. The parameters are read from
// Divisor, Mult and Offset, and cur and next must be distinct buffers. One
// division produces the quotient and the remainder together, so a walk
// allocates no new *big.Int; the result buffers grow internally when a value
// widens.
func (w *Workspace) StepBig(cur, next *big.Int) *big.Int {
	next.QuoRem(cur, w.Divisor, w.Rem)
	if w.Rem.Sign() == 0 {
		return next
	}
	next.Mul(w.Mult, cur)
	return next.Add(next, w.Offset)
}

// Step applies one instruction of the raw map in uint64 arithmetic. It is used
// only where the caller documents that no intermediate value overflows.
func Step(d, q, c, n uint64) uint64 {
	if n%d == 0 {
		return n / d
	}
	return q*n + c
}

// Gcd returns the greatest common divisor of a and b by the Euclidean
// algorithm.
func Gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// addCheck records one check and, when it fails, one failure as well.
func addCheck(t *SliceTotals, ok bool) {
	if ok {
		t.Checks++
		return
	}
	t.Checks++
	t.Failures++
}

// addCheckf records one check and prints a diagnostic when it fails.
func addCheckf(t *SliceTotals, ok bool, format string, args ...any) {
	if !ok {
		fmt.Printf("failure: "+format+"\n", args...)
	}
	addCheck(t, ok)
}

// CycleOffsets writes the offset c = 3 (8^h - 1) / 7 and the multiplier
// q = 2 c + 1 of the first slice into T0 and T1 and returns them.
func (w *Workspace) CycleOffsets(h uint64) (*big.Int, *big.Int) {
	w.T0.Sub(w.Pow(8, h), BigOne)
	w.T0.Mul(w.T0, BigThree)
	w.T1.Quo(w.T0, BigSeven)
	w.T2.SetUint64(2)
	w.T2.Mul(w.T2, w.T1)
	w.T2.Add(w.T2, BigOne)
	return w.T1, w.T2
}

// FullAccessOffsets writes the offset c = (d-1) (d^(k-1) - 1) and the
// multiplier q = (d-1) d^(k-1) + 1 of the third slice into T0 and T2 and
// returns them. It requires d >= 2 and k >= 2, and writes E with d^(k-1).
func (w *Workspace) FullAccessOffsets(d, k uint64) (*big.Int, *big.Int) {
	w.T1.SetUint64(d - 1)
	w.T0.Sub(w.Pow(d, k-1), BigOne)
	w.T0.Mul(w.T0, w.T1)
	w.T2.Mul(w.E, w.T1)
	w.T2.Add(w.T2, BigOne)
	return w.T0, w.T2
}

// sweepCycleSlice checks the first slice: for h = 0..30 the offset
// c = 3 (8^h - 1) / 7 and the multiplier q = 2 c + 1 turn the seed 3 into a
// primitive cycle of length 3 h + 1 that avoids 1. The walk verifies the
// identity 3 q + c = 3 * 2^(3h), the closed orbit formula, minimality of the
// return and the absence of 1.
func sweepCycleSlice() SliceTotals {
	var tot SliceTotals
	w := NewWorkspace()
	w.Divisor.SetUint64(2)
	for h := uint64(0); h <= cycleSliceMaxH; h++ {
		c, q := w.CycleOffsets(h)
		// 7 divides 3 (8^h - 1), so c is the integral offset.
		w.G.Sub(w.Pow(8, h), BigOne)
		w.G.Mul(w.G, BigThree)
		w.Rem.Mod(w.G, BigSeven)
		addCheckf(&tot, w.Rem.Sign() == 0, "7 does not divide 3 (8^%d - 1)", h)
		// The affine step of 3 lands on 3 * 2^(3h).
		w.G.Mul(q, BigThree)
		w.G.Add(w.G, c)
		w.T3.Lsh(BigThree, uint(3*h))
		addCheckf(&tot, w.G.Cmp(w.T3) == 0, "identity 3q+c failed at h=%d", h)
		// Walk the orbit for 3h+1 steps and compare with the closed formula.
		w.Mult.Set(q)
		w.Offset.Set(c)
		w.Cur.SetUint64(3)
		for i := uint64(1); i <= 3*h+1; i++ {
			w.StepBig(w.Cur, w.Next)
			w.Cur, w.Next = w.Next, w.Cur
			w.G.Lsh(BigThree, uint(3*h+1-i))
			addCheckf(&tot, w.Cur.Cmp(w.G) == 0,
				"orbit formula failed at h=%d, step %d", h, i)
			addCheckf(&tot, w.Cur.Cmp(BigOne) != 0,
				"orbit of the first slice contains 1 at h=%d, step %d", h, i)
			if i < 3*h+1 {
				addCheckf(&tot, w.Cur.Cmp(BigThree) != 0,
					"orbit returns early at h=%d, step %d", h, i)
			}
		}
		addCheckf(&tot, w.Cur.Cmp(BigThree) == 0,
			"orbit of the first slice does not return at h=%d", h)
		if h > 0 {
			addCheckf(&tot, c.Bit(0) == 1, "offset is even at h=%d", h)
		}
	}
	return tot
}

// sweepFullAccess checks the third slice: for d = 2..40 and k = 2..12 the
// offset c = (d-1) (d^(k-1) - 1) and the multiplier q = (d-1) d^(k-1) + 1
// satisfy q = d + c, q = c = 1 modulo d, the identity q (d-1) + c = (d-1) d^k,
// and turn the seed d - 1 into a primitive cycle of length k + 1 that avoids 1
// once d >= 3.
func sweepFullAccess() SliceTotals {
	var tot SliceTotals
	w := NewWorkspace()
	for d := uint64(2); d <= fullAccessMaxD; d++ {
		w.Divisor.SetUint64(d)
		for k := uint64(2); k <= fullAccessMaxK; k++ {
			c, q := w.FullAccessOffsets(d, k)
			// The multiplier is the base plus the offset.
			w.G.SetUint64(d)
			w.G.Add(w.G, c)
			addCheckf(&tot, w.G.Cmp(q) == 0, "q != d + c at d=%d k=%d", d, k)
			// Residues: q = c = 1 modulo d.
			w.Rem.Mod(q, w.Divisor)
			addCheckf(&tot, w.Rem.Cmp(BigOne) == 0, "q not 1 mod d at d=%d k=%d", d, k)
			w.Rem.Mod(c, w.Divisor)
			addCheckf(&tot, w.Rem.Cmp(BigOne) == 0, "c not 1 mod d at d=%d k=%d", d, k)
			// The identity q (d-1) + c = (d-1) d^k.
			w.T1.SetUint64(d - 1)
			w.Cur.Mul(q, w.T1)
			w.Cur.Add(w.Cur, c)
			w.G.SetUint64(d - 1)
			w.G.Mul(w.G, w.Pow(d, k))
			addCheckf(&tot, w.Cur.Cmp(w.G) == 0, "full-access identity failed at d=%d k=%d", d, k)
			// The orbit from d - 1: k + 1 steps back to d - 1.
			w.Mult.Set(q)
			w.Offset.Set(c)
			w.Cur.Set(w.T1)
			for i := uint64(1); i <= k+1; i++ {
				w.StepBig(w.Cur, w.Next)
				w.Cur, w.Next = w.Next, w.Cur
				w.G.SetUint64(d - 1)
				w.G.Mul(w.G, w.Pow(d, k+1-i))
				addCheckf(&tot, w.Cur.Cmp(w.G) == 0,
					"full-access orbit failed at d=%d k=%d step %d", d, k, i)
				if d >= 3 {
					addCheckf(&tot, w.Cur.Cmp(BigOne) != 0,
						"full-access orbit contains 1 at d=%d k=%d", d, k)
				}
				if i < k+1 {
					addCheckf(&tot, w.Cur.Cmp(w.T1) != 0,
						"full-access orbit returns early at d=%d k=%d step %d", d, k, i)
				}
			}
			addCheckf(&tot, w.Cur.Cmp(w.T1) == 0,
				"full-access orbit does not return at d=%d k=%d", d, k)
			if d == 2 {
				addCheckf(&tot, w.Cur.Cmp(BigOne) == 0,
					"classical instance did not reach 1 at k=%d", k)
			}
		}
	}
	return tot
}

// sweepIntersection checks the fourth slice q = d + 1, c = d - 1 for d = 3..40:
// over the seeds 1..599 and the times 0..24, a state reaches 1 exactly when it
// is the corresponding power of d, and the state 1 never returns to itself.
func sweepIntersection() SliceTotals {
	var tot SliceTotals
	w := NewWorkspace()
	for d := uint64(3); d <= intersectionMaxD; d++ {
		w.SetParams(d, d+1, d-1)
		for x := uint64(1); x <= intersectionSeeds; x++ {
			w.T0.SetUint64(x)
			w.Cur.Set(w.T0)
			for j := uint64(0); j <= intersectionMaxK; j++ {
				pow := w.Pow(d, j)
				hit := w.Cur.Cmp(BigOne) == 0
				addCheckf(&tot, hit == (w.T0.Cmp(pow) == 0),
					"intersection equivalence failed at d=%d x=%d time=%d", d, x, j)
				if j < intersectionMaxK {
					w.StepBig(w.Cur, w.Next)
					w.Cur, w.Next = w.Next, w.Cur
				}
			}
		}
		// No positive time returns the state 1 to itself.
		w.Cur.Set(BigOne)
		for j := uint64(1); j <= intersectionMaxK; j++ {
			w.StepBig(w.Cur, w.Next)
			w.Cur, w.Next = w.Next, w.Cur
			addCheckf(&tot, w.Cur.Cmp(BigOne) != 0,
				"positive power of %d returns 1 to itself at time %d", d, j)
		}
	}
	// Control: at d = 2 the equivalence fails, since 3 reaches 1 without being
	// a power of 2.
	w.SetParams(2, 3, 1)
	w.Cur.SetUint64(3)
	reached := false
	isPower := false
	for j := uint64(0); j <= intersectionMaxK; j++ {
		if w.Cur.Cmp(BigOne) == 0 {
			reached = true
		}
		if w.Pow(2, j).Cmp(BigThree) == 0 {
			isPower = true
		}
		if j < intersectionMaxK {
			w.StepBig(w.Cur, w.Next)
			w.Cur, w.Next = w.Next, w.Cur
		}
	}
	addCheckf(&tot, reached, "d=2 control: 3 does not reach 1")
	addCheckf(&tot, !isPower, "d=2 control: 3 is a power of 2")
	return tot
}

// sweepEvenOffset checks the d = 2 slice with even offsets c = 2..20: every
// seed reaches an odd state within the reach budget, and from there the orbit
// stays odd and strictly increases over the growth budget.
func sweepEvenOffset() SliceTotals {
	var tot SliceTotals
	w := NewWorkspace()
	w.Divisor.SetUint64(2)
	for c := uint64(2); c <= evenOffsetMaxC; c += 2 {
		w.Mult.SetUint64(2*c + 1)
		w.Offset.SetUint64(c)
		for n := uint64(1); n <= evenOffsetSeeds; n++ {
			w.Cur.SetUint64(n)
			steps := uint64(0)
			for w.Cur.Bit(0) == 0 && steps <= evenOffsetReach {
				w.StepBig(w.Cur, w.Next)
				w.Cur, w.Next = w.Next, w.Cur
				steps++
			}
			addCheckf(&tot, steps <= evenOffsetReach,
				"even offset c=%d seed %d did not reach an odd state", c, n)
			addCheckf(&tot, w.Cur.Bit(0) == 1, "reached state not odd at c=%d seed %d", c, n)
			cur, nxt := w.Cur, w.Next
			for i := uint64(0); i < evenOffsetGrowth; i++ {
				w.StepBig(cur, nxt)
				addCheckf(&tot, nxt.Bit(0) == 1, "growth state not odd at c=%d seed %d", c, n)
				addCheckf(&tot, nxt.Cmp(cur) > 0,
					"growth not strict at c=%d seed %d step %d", c, n, i)
				cur, nxt = nxt, cur
			}
		}
	}
	return tot
}

// sweepOddOffset checks the d = 2 slice with odd offsets c = 1..41: the step
// preserves the divisor gcd with c on the seeds 1..2000, every divisor of c
// occurs as such a gcd, and for c > 1 the seed c itself avoids 1 over
// oddOffsetCaptureSteps steps.
func sweepOddOffset() SliceTotals {
	var tot SliceTotals
	w := NewWorkspace()
	for c := uint64(1); c <= oddOffsetMaxC; c += 2 {
		q := 2*c + 1
		for n := uint64(1); n <= oddOffsetSeeds; n++ {
			got := Gcd(Step(2, q, c, n), c)
			addCheckf(&tot, got == Gcd(n, c), "gcd not preserved at c=%d n=%d", c, n)
		}
		for e := uint64(1); e <= c; e++ {
			if c%e != 0 {
				continue
			}
			found := uint64(0)
			for n := uint64(1); n <= oddOffsetSeeds; n++ {
				if Gcd(n, c) == e {
					found = n
					break
				}
			}
			addCheckf(&tot, found != 0, "stratum %d of c=%d is not realized", e, c)
		}
		if c > 1 {
			w.SetParams(2, q, c)
			w.Cur.SetUint64(c)
			for k := 0; k < oddOffsetCaptureSteps; k++ {
				w.StepBig(w.Cur, w.Next)
				w.Cur, w.Next = w.Next, w.Cur
				addCheckf(&tot, w.Cur.Cmp(BigOne) != 0,
					"seed %d of c=%d reached 1 at step %d", c, c, k+1)
			}
		}
	}
	return tot
}

// main runs the five sweeps concurrently, sums their totals, prints the
// certificate line and exits nonzero when any check failed.
func main() {
	sweeps := []func() SliceTotals{
		sweepCycleSlice,
		sweepFullAccess,
		sweepIntersection,
		sweepEvenOffset,
		sweepOddOffset,
	}
	results := make([]SliceTotals, len(sweeps))
	var wg sync.WaitGroup
	for i, sweep := range sweeps {
		wg.Add(1)
		go func(i int, sweep func() SliceTotals) {
			defer wg.Done()
			results[i] = sweep()
		}(i, sweep)
	}
	wg.Wait()
	var checks, failures uint64
	for _, r := range results {
		checks += r.Checks
		failures += r.Failures
	}
	fmt.Printf("relations cycles checks: %d, failures: %d\n", checks, failures)
	if failures != 0 {
		os.Exit(1)
	}
}
