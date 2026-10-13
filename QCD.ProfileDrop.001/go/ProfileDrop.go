// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"fmt"
	"os"
	"sync"
)

// The executable checks this finite rectangle, not all integer parameters.
const (
	GridQMin               int64 = -5
	GridQMax               int64 = 5
	GridCMin               int64 = -5
	GridCMax               int64 = 5
	GridMMin               int64 = 2
	GridMMax               int64 = 6
	GridNMin               int64 = -8
	GridNMax               int64 = 8
	OrbitSteps                   = 8
	WorkerCount                  = 8
	OrbitStateBound        int64 = 7128905
	ArithmeticOperandBound int64 = 42773435
)

// Workspace retains one parameter slice's counters without allocating in its loops.
type Workspace struct {
	Checks     uint64
	Failures   uint64
	CycleCases uint64
}

// EqualReports supplies exact integer equality to the certificate.
func EqualReports(got, want int64) bool {
	return got == want
}

// ConstantTrue is a negative control: it also accepts unequal integers.
func ConstantTrue(got, want int64) bool {
	return true
}

// PredicateSeparates tests both agreement and refusal before accepting a comparison.
func PredicateSeparates(pred func(got, want int64) bool) bool {
	return pred != nil && pred(7, 7) && !pred(7, 8)
}

// CheckParameters restricts products to the documented finite parameter domain.
func CheckParameters(q, c int64) {
	if q < GridQMin || q > GridQMax || (-2 < q && q < 2) ||
		c < GridCMin || c > GridCMax {
		panic("parameters outside the certified grid")
	}
}

// CheckModulus protects the fixed-width residue mask and the positive remainder.
func CheckModulus(m int64) {
	if m < GridMMin || m > GridMMax {
		panic("modulus outside the certified grid")
	}
}

// CheckOperand excludes integer negation overflow and bounds primitive arithmetic.
func CheckOperand(n int64) {
	if n < -ArithmeticOperandBound || n > ArithmeticOperandBound {
		panic("operand outside the certified arithmetic bound")
	}
}

// CheckResidue rejects representatives outside the finite map's state space.
func CheckResidue(m, r int64) {
	CheckModulus(m)
	if r < 0 || r >= m {
		panic("residue outside the modulus")
	}
}

// CheckSeed bounds the inputs of the one-step and two-step grid identities.
func CheckSeed(n int64) {
	if n < GridNMin || n > GridNMax {
		panic("seed outside the certified grid")
	}
}

// AbsInt takes magnitude only after excluding unsupported operands, including MinInt64.
func AbsInt(n int64) int64 {
	CheckOperand(n)
	if n < 0 {
		return -n
	}
	return n
}

// EuclideanMod returns the nonnegative remainder on the bounded operand domain.
func EuclideanMod(n, m int64) int64 {
	CheckOperand(n)
	CheckModulus(m)
	r := n % m
	if r < 0 {
		r += m
	}
	return r
}

// Displacement evaluates (q-1)n+c; its intermediate magnitude is below 2^28.
func Displacement(q, c, n int64) int64 {
	CheckParameters(q, c)
	CheckOperand(n)
	return (q-1)*n + c
}

// Affine evaluates qn+c; its intermediate magnitude is below 2^28.
func Affine(q, c, n int64) int64 {
	CheckParameters(q, c)
	CheckOperand(n)
	return q*n + c
}

// DisplacementIdentity checks one affine step on the seed rectangle.
func DisplacementIdentity(q, c, n int64) bool {
	CheckSeed(n)
	return Displacement(q, c, Affine(q, c, n)) == q*Displacement(q, c, n)
}

// ResidueIdentity checks compatibility of the affine branch with the finite map.
func ResidueIdentity(q, c, n, m int64) bool {
	CheckSeed(n)
	r := EuclideanMod(n, m)
	return EuclideanMod(Affine(q, c, n), m) == EuclideanMod(Affine(q, c, r), m)
}

// TwoStepIdentity checks the square multiplier on the seed rectangle.
func TwoStepIdentity(q, c, n int64) bool {
	CheckSeed(n)
	return Displacement(q, c, Affine(q, c, Affine(q, c, n))) ==
		q*(q*Displacement(q, c, n))
}

// Divides tests only the documented nonzero signed divisors and bounded operands.
func Divides(d, n int64) bool {
	if d < -GridMMax || d > GridMMax || (-GridMMin < d && d < GridMMin) {
		panic("divisor outside the certified grid")
	}
	CheckOperand(n)
	return n%d == 0
}

// SameDivisorSign checks divisibility, not equality of the two signed quotients.
func SameDivisorSign(d, n int64) bool {
	return Divides(d, n) == Divides(-d, n)
}

// HasZeroAvoidingCycle returns a repeated nonzero residue on a cycle.
// There are m-1 nonzero states: m inspections either meet zero or detect repetition.
func HasZeroAvoidingCycle(q, c, m int64) (int64, bool) {
	CheckParameters(q, c)
	CheckModulus(m)
	for start := int64(1); start < m; start++ {
		var seen uint64
		r := start
		for step := int64(0); step < m; step++ {
			if r == 0 {
				break
			}
			bit := uint64(1) << uint(r)
			if seen&bit != 0 {
				return r, true
			}
			seen |= bit
			r = EuclideanMod(Affine(q, c, r), m)
		}
	}
	return 0, false
}

// CycleLength checks that the supplied residue itself lies on a nonzero cycle.
func CycleLength(q, c, m, start int64) int64 {
	CheckParameters(q, c)
	CheckResidue(m, start)
	if start == 0 {
		return 0
	}
	r := start
	for period := int64(1); period < m; period++ {
		r = EuclideanMod(Affine(q, c, r), m)
		if r == 0 {
			return 0
		}
		if r == start {
			return period
		}
	}
	return 0
}

// ReachesZero checks all possible transient positions before the first repetition.
func ReachesZero(q, c, m, start int64) bool {
	CheckParameters(q, c)
	CheckResidue(m, start)
	r := start
	for step := int64(0); step < m; step++ {
		if r == 0 {
			return true
		}
		r = EuclideanMod(Affine(q, c, r), m)
	}
	return r == 0
}

// PositiveLift selects r+m or r+2m; their displacements differ by (q-1)m != 0.
func PositiveLift(q, c, m, r int64) (int64, bool) {
	CheckParameters(q, c)
	CheckResidue(m, r)
	first := r + m
	if Displacement(q, c, first) != 0 {
		return first, true
	}
	second := r + 2*m
	if Displacement(q, c, second) != 0 {
		return second, true
	}
	return 0, false
}

// Record retains each comparison even when an earlier comparison failed.
func Record(w *Workspace, ok bool) {
	w.Checks++
	if !ok {
		w.Failures++
	}
}

// CheckOrbit compares all nine visited states with the two-coordinate recurrence.
func CheckOrbit(q, c, m, seed int64, pred func(got, want int64) bool, w *Workspace) {
	state := seed
	z := Displacement(q, c, seed)
	r := EuclideanMod(seed, m)
	for step := 0; step < OrbitSteps; step++ {
		Record(w, r != 0)
		Record(w, !Divides(m, state))
		next := Affine(q, c, state)
		Record(w, pred(Displacement(q, c, next), q*z))
		nextResidue := EuclideanMod(Affine(q, c, r), m)
		Record(w, pred(EuclideanMod(next, m), nextResidue))
		state = next
		z = q * z
		r = nextResidue
	}
	Record(w, r != 0)
	Record(w, !Divides(m, state))
	Record(w, AbsInt(state) > AbsInt(seed))
}

// CheckQ checks one multiplier slice with its own counters and no shared writes.
func CheckQ(q int64, pred func(got, want int64) bool, w *Workspace) {
	CheckParameters(q, 0)
	for c := GridCMin; c <= GridCMax; c++ {
		for n := GridNMin; n <= GridNMax; n++ {
			Record(w, pred(Displacement(q, c, Affine(q, c, n)), q*Displacement(q, c, n)))
			Record(w, pred(Displacement(q, c, Affine(q, c, Affine(q, c, n))),
				q*(q*Displacement(q, c, n))))
		}
		for m := GridMMin; m <= GridMMax; m++ {
			for n := GridNMin; n <= GridNMax; n++ {
				r := EuclideanMod(n, m)
				Record(w, pred(EuclideanMod(Affine(q, c, n), m),
					EuclideanMod(Affine(q, c, r), m)))
			}
			cycle, found := HasZeroAvoidingCycle(q, c, m)
			allDie := true
			for start := int64(0); start < m; start++ {
				if !ReachesZero(q, c, m, start) {
					allDie = false
				}
			}
			Record(w, found != allDie)
			if !found {
				continue
			}
			w.CycleCases++
			Record(w, CycleLength(q, c, m, cycle) > 0)
			seed, ok := PositiveLift(q, c, m, cycle)
			Record(w, ok)
			if !ok {
				continue
			}
			Record(w, EuclideanMod(seed, m) == cycle)
			Record(w, Displacement(q, c, seed) != 0)
			CheckOrbit(q, c, m, seed, pred, w)
		}
	}
}

// CheckSigns adds the bounded signed-divisor checks after combining worker counters.
func CheckSigns(w *Workspace) {
	for d := GridMMin; d <= GridMMax; d++ {
		for n := int64(-20); n <= 20; n++ {
			Record(w, SameDivisorSign(d, n))
		}
	}
}

// CheckGrid runs sequentially for allocation and injected-comparison tests.
func CheckGrid(pred func(got, want int64) bool) Workspace {
	if pred == nil {
		panic("nil comparison predicate")
	}
	var w Workspace
	Record(&w, PredicateSeparates(pred))
	for q := GridQMin; q <= GridQMax; q++ {
		if -2 < q && q < 2 {
			continue
		}
		CheckQ(q, pred, &w)
	}
	CheckSigns(&w)
	return w
}

// CheckGridParallel assigns each of the eight multiplier slices to one goroutine.
// The supplied predicate must be concurrency-safe; EqualReports is a pure comparison.
// Worker storage is fixed before launch; only the final reduction reads all counters.
func CheckGridParallel(pred func(got, want int64) bool) Workspace {
	if pred == nil {
		panic("nil comparison predicate")
	}
	var workers [WorkerCount]Workspace
	var wg sync.WaitGroup
	index := 0
	for q := GridQMin; q <= GridQMax; q++ {
		if -2 < q && q < 2 {
			continue
		}
		wg.Add(1)
		go CheckQWorker(q, pred, &workers[index], &wg)
		index++
	}
	wg.Wait()
	var w Workspace
	Record(&w, PredicateSeparates(pred))
	for _, worker := range workers {
		w.Checks += worker.Checks
		w.Failures += worker.Failures
		w.CycleCases += worker.CycleCases
	}
	CheckSigns(&w)
	return w
}

// CheckQWorker closes exactly the WaitGroup slot owned by this multiplier slice.
func CheckQWorker(q int64, pred func(got, want int64) bool, w *Workspace,
	wg *sync.WaitGroup) {
	defer wg.Done()
	CheckQ(q, pred, w)
}

// main prints bounded certificate totals and fails when any comparison was rejected.
func main() {
	w := CheckGridParallel(EqualReports)
	fmt.Printf("finite checks: %d; zero-avoiding parameter cases: %d/440\n",
		w.Checks, w.CycleCases)
	if w.Failures != 0 {
		fmt.Fprintf(os.Stderr, "failures: %d\n", w.Failures)
		os.Exit(1)
	}
}
