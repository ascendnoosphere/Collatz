// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedTraps checks finite instances of the signed trap
// classification. A raw orbit that never divides follows one affine
// recursion, and the multiplier decides its future: a constant fixed point, a
// nonzero translation, the two-cycle (n, c-n), the affine fixed point, or
// escape in absolute value. The sweep also checks the residue walk that
// decides divisibility. All arithmetic is signed and exact.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Grid of the certificate. The offset-sum sweep uses the multiplier range
// [-signedTrapMaxQ, signedTrapMaxQ] and the index range [0, signedTrapMaxJ];
// the itinerary and classification sweeps use the multiplier and offset range
// [-signedOffsetMax, signedOffsetMax]; the walks use the divisors of
// SignedDivisorList and the seeds of signedSeedList over signedHorizon steps;
// the residue sweep uses the moduli two up to signedResidueMax. With |q| <= 6
// and j <= 24 the largest offset sum is below 6^24 < 2^63. An orbit with
// |q| <= 6 and |n| + |c| <= 30 need not fit in an int64, since
// 6^24 * 30 > 2^63, so the orbit sweep drops that multiplier range and uses
// |q| <= 4, where 4^24 * 30 < 2^59. Every value on these grids fits in an int64.
const (
	signedTrapMaxQ    = 6
	signedTrapMaxJ    = 24
	signedOffsetMax   = 4
	signedHorizon     = 24
	signedEscapeBound = 1 << 20
	signedResidueMax  = 12
	signedWorkers     = 4
)

// Totals counts checks and failures of one slice.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// Check records one comparison.
func (t *Totals) Check(ok bool) {
	t.Checks++
	if !ok {
		t.Failures++
	}
}

// Workspace holds the reusable orbit buffer of the walks.
type Workspace struct {
	Orbit []int64
}

// NewWorkspace returns a workspace with a buffer for the longest walk.
func NewWorkspace() *Workspace {
	return &Workspace{Orbit: make([]int64, 0, signedHorizon+2)}
}

// TrapSumInt returns the chronological offset sum of j affine steps with
// multiplier q, that is the sum of q^0 up to q^(j-1).
func TrapSumInt(q int64, j int) int64 {
	sum := int64(0)
	pow := int64(1)
	for i := 0; i < j; i++ {
		sum += pow
		pow *= q
	}
	return sum
}

// PowInt returns q to the j-th power on the documented grid.
func PowInt(q int64, j int) int64 {
	out := int64(1)
	for i := 0; i < j; i++ {
		out *= q
	}
	return out
}

// SignedStep applies one raw step with the signed multiplier q, offset c and
// divisor D. An exactly divisible state is divided, otherwise the affine
// branch runs. Go truncates toward zero, which is the exact quotient when D
// divides n, so both signs and negative divisors are covered on every value
// the sweeps use. The quotient of the most negative int64 by -1 is not
// representable and is not evaluated.
func SignedStep(q, c, D, n int64) int64 {
	if n%D == 0 {
		return n / D
	}
	return q*n + c
}

// ResidueStep maps one residue of the affine branch modulo m with m > 0.
func ResidueStep(q, c, m, r int64) int64 {
	v := (q*r + c) % m
	if v < 0 {
		v += m
	}
	return v
}

// Residue maps a signed state to its representative in [0, m).
func Residue(n, m int64) int64 {
	v := n % m
	if v < 0 {
		v += m
	}
	return v
}

// SignedDivisorList returns the signed divisors of the sweeps.
func SignedDivisorList() []int64 {
	return []int64{-5, -3, -2, 2, 3, 5}
}

// SignedSeedList returns the seeds of the sweeps; the list contains signed
// values and zero.
func SignedSeedList() []int64 {
	return []int64{-13, -7, -3, -1, 0, 1, 2, 6, 11, 25}
}

// AbsInt returns the absolute value of a signed integer.
func AbsInt(n int64) int64 {
	if n < 0 {
		return -n
	}
	return n
}

// SweepTrapSum checks the offset-sum identities over the multiplier and index
// grid: the shifted geometric series, the one-step recursion, the extension by
// two steps, and the degenerate multipliers zero, one and negative one.
func SweepTrapSum(t *Totals) {
	for q := int64(-signedTrapMaxQ); q <= signedTrapMaxQ; q++ {
		for j := 0; j <= signedTrapMaxJ; j++ {
			sum := TrapSumInt(q, j)
			pow := PowInt(q, j)
			t.Check((q-1)*sum == pow-1)
			if j < signedTrapMaxJ {
				t.Check(TrapSumInt(q, j+1) == q*sum+1)
			}
			if j+2 <= signedTrapMaxJ {
				t.Check(TrapSumInt(q, j+2) == sum+pow+PowInt(q, j+1))
			}
			switch q {
			case 0:
				if j >= 1 {
					t.Check(sum == 1)
				}
			case 1:
				t.Check(sum == int64(j))
			case -1:
				if j%2 == 0 {
					t.Check(sum == 0)
				} else {
					t.Check(sum == 1)
				}
			}
		}
	}
}

// SweepItineraryQ checks, on every division-free prefix of the walks with one
// multiplier, that the orbit equals the affine formula with the offset sum and
// that the residue walk casts the orbit. Once the walk divides the affine
// formula is no longer claimed there and the prefix checks stop. The walk keeps
// its state in locals, so no workspace is needed.
func SweepItineraryQ(q int64, _ *Workspace, t *Totals) {
	for c := int64(-signedOffsetMax); c <= signedOffsetMax; c++ {
		for _, D := range SignedDivisorList() {
			m := AbsInt(D)
			for _, n := range SignedSeedList() {
				cur := n
				res := Residue(n, m)
				clean := true
				for j := 0; j <= signedHorizon && clean; j++ {
					t.Check(res == Residue(cur, m))
					t.Check(cur == PowInt(q, j)*n+c*TrapSumInt(q, j))
					if cur%D == 0 {
						clean = false
					}
					cur = SignedStep(q, c, D, cur)
					res = ResidueStep(q, c, m, res)
				}
			}
		}
	}
}

// ClassificationQ walks the orbit grid of one multiplier; walks that divide
// are skipped, because the classification is claimed only on division-free
// orbits.
func ClassificationQ(q int64, w *Workspace, t *Totals) {
	for c := int64(-signedOffsetMax); c <= signedOffsetMax; c++ {
		for _, D := range SignedDivisorList() {
			for _, n := range SignedSeedList() {
				orbit := FillOrbit(w.Orbit, q, c, D, n)
				ClassifyOrbit(orbit, q, c, n, D, t)
			}
		}
	}
}

// ClassifyOrbit checks the classification instance of one walk: a zero
// multiplier gives the constant offset, the unit multiplier gives a
// translation with escape for a nonzero offset, the negative unit multiplier
// gives the reflection pair, and an expanding multiplier with a nonfixed state
// escapes.
func ClassifyOrbit(orbit []int64, q, c, n, D int64, t *Totals) {
	if !DivisionFree(orbit, D) {
		return
	}
	switch {
	case q == 0:
		for j := 1; j+1 < len(orbit); j++ {
			t.Check(orbit[j] == c)
		}
	case q == 1:
		for j := 0; j+1 < len(orbit); j++ {
			t.Check(orbit[j] == n+int64(j)*c)
		}
		if c != 0 {
			// The translation grows without bound; on the horizon a state
			// beyond the offset must be followed by a strictly larger one.
			grew := false
			for j := 0; j+1 < len(orbit); j++ {
				if AbsInt(orbit[j]) > AbsInt(c) && AbsInt(orbit[j+1]) > AbsInt(orbit[j]) {
					grew = true
				}
			}
			t.Check(grew)
		}
	case q == -1:
		for j := 0; j+1 < len(orbit); j++ {
			if j%2 == 0 {
				t.Check(orbit[j] == n)
			} else {
				t.Check(orbit[j] == c-n)
			}
		}
	default:
		if (q-1)*n+c == 0 {
			for j := 0; j+1 < len(orbit); j++ {
				t.Check(orbit[j] == n)
			}
		} else {
			t.Check(Escapes(orbit))
		}
	}
}

// SweepResidues checks the residue map of the affine branch modulo every
// modulus from two to signedResidueMax against the cast of the raw step.
func SweepResidues(t *Totals) {
	for m := int64(2); m <= signedResidueMax; m++ {
		for q := int64(-signedOffsetMax); q <= signedOffsetMax; q++ {
			for c := int64(-signedOffsetMax); c <= signedOffsetMax; c++ {
				for r := int64(0); r < m; r++ {
					t.Check(ResidueStep(q, c, m, r) == Residue(q*r+c, m))
				}
			}
		}
	}
}

// SweepControls checks the documented boundary cases: the divisor one makes
// every state divisible, a zero offset reaches zero and then divides, a state
// on the affine fixed-point equation is constant, and a walk that divides
// leaves the affine formula, so the certificate must not claim the
// classification there. The zero-offset tail is a raw walk, not a trap.
func SweepControls(w *Workspace, t *Totals) {
	orbit := FillOrbit(w.Orbit, 2, 1, 1, 9)
	for j := 0; j+1 < len(orbit); j++ {
		t.Check(orbit[j] == 9)
	}
	orbit = FillOrbit(w.Orbit, 0, 0, 3, 7)
	for j := 1; j+1 < len(orbit); j++ {
		t.Check(orbit[j] == 0)
	}
	orbit = FillOrbit(w.Orbit, 1, 0, 5, -4)
	for j := 0; j+1 < len(orbit); j++ {
		t.Check(orbit[j] == -4)
	}
	orbit = FillOrbit(w.Orbit, 2, -4, 3, 4)
	for j := 0; j+1 < len(orbit); j++ {
		t.Check(orbit[j] == 4)
	}
	orbit = FillOrbit(w.Orbit, -1, 0, 7, 5)
	for j := 0; j+1 < len(orbit); j++ {
		if j%2 == 0 {
			t.Check(orbit[j] == 5)
		} else {
			t.Check(orbit[j] == -5)
		}
	}
	orbit = FillOrbit(w.Orbit, 2, 1, 3, 9)
	t.Check(orbit[0] == 9)
	t.Check(orbit[1] == 3)
	t.Check(orbit[2] == 1)
	t.Check(orbit[3] == 3)
	t.Check(!DivisionFree(orbit, 3))
	t.Check(orbit[1] != 2*9+1)
}

// FillOrbit writes n and its horizon successors under the raw step into buf
// and returns the buffer with signedHorizon+1 states.
func FillOrbit(buf []int64, q, c, D, n int64) []int64 {
	buf = buf[:0]
	cur := n
	for j := 0; j <= signedHorizon; j++ {
		buf = append(buf, cur)
		cur = SignedStep(q, c, D, cur)
	}
	return buf
}

// DivisionFree reports whether no state before the last one is divisible by D.
func DivisionFree(orbit []int64, D int64) bool {
	for j := 0; j+1 < len(orbit); j++ {
		if orbit[j]%D == 0 {
			return false
		}
	}
	return true
}

// Escapes reports whether some state of the orbit exceeds the escape bound in
// absolute value.
func Escapes(orbit []int64) bool {
	for _, state := range orbit {
		if AbsInt(state) > signedEscapeBound {
			return true
		}
	}
	return false
}

// RunMultiplierSweep chunks the multiplier range over the workers and runs one
// walk sweep per multiplier; every chunk gets its own workspace, and the
// chunk totals are summed in a fixed order.
func RunMultiplierSweep(fn func(int64, *Workspace, *Totals)) Totals {
	count := 2*signedOffsetMax + 1
	width := (count + signedWorkers - 1) / signedWorkers
	chunks := make([]Totals, signedWorkers)
	var wg sync.WaitGroup
	for i := 0; i < signedWorkers; i++ {
		lo := int64(-signedOffsetMax + i*width)
		hi := lo + int64(width) - 1
		if lo > signedOffsetMax {
			continue
		}
		if hi > signedOffsetMax {
			hi = signedOffsetMax
		}
		wg.Add(1)
		go func(idx int, lo, hi int64) {
			defer wg.Done()
			w := NewWorkspace()
			for q := lo; q <= hi; q++ {
				fn(q, w, &chunks[idx])
			}
		}(i, lo, hi)
	}
	wg.Wait()
	var total Totals
	for _, chunk := range chunks {
		total.Checks += chunk.Checks
		total.Failures += chunk.Failures
	}
	return total
}

// main runs every slice, prints the certificate and exits nonzero on failure.
func main() {
	sum := Totals{}
	SweepTrapSum(&sum)
	fmt.Printf("%-14s checks %8d failures %d\n", "offset sums", sum.Checks, sum.Failures)

	itinerary := RunMultiplierSweep(SweepItineraryQ)
	fmt.Printf("%-14s checks %8d failures %d\n", "itinerary",
		itinerary.Checks, itinerary.Failures)

	classes := RunMultiplierSweep(ClassificationQ)
	fmt.Printf("%-14s checks %8d failures %d\n", "classification",
		classes.Checks, classes.Failures)

	residues := Totals{}
	SweepResidues(&residues)
	fmt.Printf("%-14s checks %8d failures %d\n", "residues",
		residues.Checks, residues.Failures)

	controls := Totals{}
	SweepControls(NewWorkspace(), &controls)
	fmt.Printf("%-14s checks %8d failures %d\n", "controls",
		controls.Checks, controls.Failures)

	total := Totals{}
	for _, part := range []Totals{sum, itinerary, classes, residues, controls} {
		total.Checks += part.Checks
		total.Failures += part.Failures
	}
	fmt.Printf("signed trap checks: %d, failures: %d\n", total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
