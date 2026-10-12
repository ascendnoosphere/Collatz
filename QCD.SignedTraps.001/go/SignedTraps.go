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
// signedDivisorList and the seeds of signedSeedList over signedHorizon steps;
// the residue sweep uses the moduli two up to signedResidueMax. With |q| <= 6
// and j <= 24 the largest offset sum is below 6^24 < 2^63, and with |q| <= 6
// and |n| + |c| <= 30 the orbit within the horizon stays below 6^24 * 30 <
// 2^68, so the orbit sweep keeps the multiplier range of the sum sweep out and
// uses |q| <= 4, where 4^24 * 30 < 2^59. Every value fits in an int64.
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

// check records one comparison.
func (t *Totals) check(ok bool) {
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
// divides n, so both signs and negative divisors are covered.
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

// signedDivisorList returns the signed divisors of the sweeps.
func signedDivisorList() []int64 {
	return []int64{-5, -3, -2, 2, 3, 5}
}

// signedSeedList returns the seeds of the sweeps; the list contains signed
// values and zero.
func signedSeedList() []int64 {
	return []int64{-13, -7, -3, -1, 0, 1, 2, 6, 11, 25}
}

// absInt returns the absolute value of a signed integer.
func absInt(n int64) int64 {
	if n < 0 {
		return -n
	}
	return n
}

// sweepTrapSum checks the offset-sum identities over the multiplier and index
// grid: the shifted geometric series, the one-step recursion, the extension by
// two steps, and the degenerate multipliers zero, one and negative one.
func sweepTrapSum(t *Totals) {
	for q := int64(-signedTrapMaxQ); q <= signedTrapMaxQ; q++ {
		for j := 0; j <= signedTrapMaxJ; j++ {
			sum := TrapSumInt(q, j)
			pow := PowInt(q, j)
			t.check((q-1)*sum == pow-1)
			if j < signedTrapMaxJ {
				t.check(TrapSumInt(q, j+1) == q*sum+1)
			}
			if j+2 <= signedTrapMaxJ {
				t.check(TrapSumInt(q, j+2) == sum+pow+PowInt(q, j+1))
			}
			switch q {
			case 0:
				if j >= 1 {
					t.check(sum == 1)
				}
			case 1:
				t.check(sum == int64(j))
			case -1:
				if j%2 == 0 {
					t.check(sum == 0)
				} else {
					t.check(sum == 1)
				}
			}
		}
	}
}

// sweepItineraryQ checks, on every division-free prefix of the walks with one
// multiplier, that the orbit equals the affine formula with the offset sum and
// that the residue walk casts the orbit. Once the walk divides the affine
// formula is no longer claimed there and the prefix checks stop. The walk keeps
// its state in locals, so no workspace is needed.
func sweepItineraryQ(q int64, _ *Workspace, t *Totals) {
	for c := int64(-signedOffsetMax); c <= signedOffsetMax; c++ {
		for _, D := range signedDivisorList() {
			m := absInt(D)
			for _, n := range signedSeedList() {
				cur := n
				res := Residue(n, m)
				clean := true
				for j := 0; j <= signedHorizon && clean; j++ {
					t.check(res == Residue(cur, m))
					t.check(cur == PowInt(q, j)*n+c*TrapSumInt(q, j))
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

// classificationQ walks the orbit grid of one multiplier; walks that divide
// are skipped, because the classification is claimed only on division-free
// orbits.
func classificationQ(q int64, w *Workspace, t *Totals) {
	for c := int64(-signedOffsetMax); c <= signedOffsetMax; c++ {
		for _, D := range signedDivisorList() {
			for _, n := range signedSeedList() {
				orbit := fillOrbit(w.Orbit, q, c, D, n)
				classifyOrbit(orbit, q, c, n, D, t)
			}
		}
	}
}

// classifyOrbit checks the classification instance of one walk: a zero
// multiplier gives the constant offset, the unit multiplier gives a
// translation with escape for a nonzero offset, the negative unit multiplier
// gives the reflection pair, and an expanding multiplier with a nonfixed state
// escapes.
func classifyOrbit(orbit []int64, q, c, n, D int64, t *Totals) {
	if !divisionFree(orbit, D) {
		return
	}
	switch {
	case q == 0:
		for j := 1; j+1 < len(orbit); j++ {
			t.check(orbit[j] == c)
		}
	case q == 1:
		for j := 0; j+1 < len(orbit); j++ {
			t.check(orbit[j] == n+int64(j)*c)
		}
		if c != 0 {
			// The translation grows without bound; on the horizon a state
			// beyond the offset must be followed by a strictly larger one.
			grew := false
			for j := 0; j+1 < len(orbit); j++ {
				if absInt(orbit[j]) > absInt(c) && absInt(orbit[j+1]) > absInt(orbit[j]) {
					grew = true
				}
			}
			t.check(grew)
		}
	case q == -1:
		for j := 0; j+1 < len(orbit); j++ {
			if j%2 == 0 {
				t.check(orbit[j] == n)
			} else {
				t.check(orbit[j] == c-n)
			}
		}
	default:
		if (q-1)*n+c == 0 {
			for j := 0; j+1 < len(orbit); j++ {
				t.check(orbit[j] == n)
			}
		} else {
			t.check(escapes(orbit))
		}
	}
}

// sweepResidues checks the residue map of the affine branch modulo every
// modulus from two to signedResidueMax against the cast of the raw step.
func sweepResidues(t *Totals) {
	for m := int64(2); m <= signedResidueMax; m++ {
		for q := int64(-signedOffsetMax); q <= signedOffsetMax; q++ {
			for c := int64(-signedOffsetMax); c <= signedOffsetMax; c++ {
				for r := int64(0); r < m; r++ {
					t.check(ResidueStep(q, c, m, r) == Residue(q*r+c, m))
				}
			}
		}
	}
}

// sweepControls checks the documented boundary cases: the divisor one makes
// every state divisible, the degenerate traps are fixed points, a state on the
// affine fixed-point equation is constant, and a walk that divides leaves the
// affine formula, so the certificate must not claim the classification there.
func sweepControls(w *Workspace, t *Totals) {
	orbit := fillOrbit(w.Orbit, 2, 1, 1, 9)
	for j := 0; j+1 < len(orbit); j++ {
		t.check(orbit[j] == 9)
	}
	orbit = fillOrbit(w.Orbit, 0, 0, 3, 7)
	for j := 1; j+1 < len(orbit); j++ {
		t.check(orbit[j] == 0)
	}
	orbit = fillOrbit(w.Orbit, 1, 0, 5, -4)
	for j := 0; j+1 < len(orbit); j++ {
		t.check(orbit[j] == -4)
	}
	orbit = fillOrbit(w.Orbit, 2, -4, 3, 4)
	for j := 0; j+1 < len(orbit); j++ {
		t.check(orbit[j] == 4)
	}
	orbit = fillOrbit(w.Orbit, -1, 0, 7, 5)
	for j := 0; j+1 < len(orbit); j++ {
		if j%2 == 0 {
			t.check(orbit[j] == 5)
		} else {
			t.check(orbit[j] == -5)
		}
	}
	orbit = fillOrbit(w.Orbit, 2, 1, 3, 9)
	t.check(orbit[0] == 9)
	t.check(orbit[1] == 3)
	t.check(orbit[2] == 1)
	t.check(orbit[3] == 3)
	t.check(!divisionFree(orbit, 3))
	t.check(orbit[1] != 2*9+1)
}

// fillOrbit writes n and its horizon successors under the raw step into buf
// and returns the buffer with signedHorizon+1 states.
func fillOrbit(buf []int64, q, c, D, n int64) []int64 {
	buf = buf[:0]
	cur := n
	for j := 0; j <= signedHorizon; j++ {
		buf = append(buf, cur)
		cur = SignedStep(q, c, D, cur)
	}
	return buf
}

// divisionFree reports whether no state before the last one is divisible by D.
func divisionFree(orbit []int64, D int64) bool {
	for j := 0; j+1 < len(orbit); j++ {
		if orbit[j]%D == 0 {
			return false
		}
	}
	return true
}

// escapes reports whether some state of the orbit exceeds the escape bound in
// absolute value.
func escapes(orbit []int64) bool {
	for _, state := range orbit {
		if absInt(state) > signedEscapeBound {
			return true
		}
	}
	return false
}

// runMultiplierSweep chunks the multiplier range over the workers and runs one
// walk sweep per multiplier; every chunk gets its own workspace, and the
// chunk totals are summed in a fixed order.
func runMultiplierSweep(fn func(int64, *Workspace, *Totals)) Totals {
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
	sweepTrapSum(&sum)
	fmt.Printf("%-14s checks %8d failures %d\n", "offset sums", sum.Checks, sum.Failures)

	itinerary := runMultiplierSweep(sweepItineraryQ)
	fmt.Printf("%-14s checks %8d failures %d\n", "itinerary",
		itinerary.Checks, itinerary.Failures)

	classes := runMultiplierSweep(classificationQ)
	fmt.Printf("%-14s checks %8d failures %d\n", "classification",
		classes.Checks, classes.Failures)

	residues := Totals{}
	sweepResidues(&residues)
	fmt.Printf("%-14s checks %8d failures %d\n", "residues",
		residues.Checks, residues.Failures)

	controls := Totals{}
	sweepControls(NewWorkspace(), &controls)
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
