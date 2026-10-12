// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere
//
// Exact finite certificates for the residue-access family. The program
// recomputes the residue orbit of zero, the access modulus, the least return
// time and the prime-case conclusions on bounded sweeps, and reports one
// counter per checked instance. It proves nothing by itself; the Lean module
// carries the theorems, and the certificate exists to make the arithmetic
// executable.

package main

import (
	"fmt"
	"math/big"
	"os"
	"sync"
)

// bigOne is the constant one used in subtractions.
var bigOne = big.NewInt(1)

// Sweep bounds. The residue arithmetic stays below 2^58: states are reduced
// modulo D, and D is at most three hundred, so every product stays small.
const (
	accessMaxQ     = 24
	accessMaxC     = 12
	accessMaxD     = 24
	accessMaxJ     = 20
	accessPrimeQ   = 40
	accessOrderCap = 300
	accessWorkers  = 4
)

// Totals counts checks and failures of one sweep or of a whole run.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// check adds one checked instance and records a failure when it does not hold.
func (t *Totals) check(ok bool) {
	t.Checks++
	if !ok {
		t.Failures++
	}
}

// Workspace holds reusable big integers so that no fresh value is allocated
// per instance. Buffers may grow internally as values widen.
type Workspace struct {
	Pow  big.Int
	Base big.Int
	Mod  big.Int
	Acc  big.Int
	Exp  big.Int
}

// NewWorkspace returns a workspace with an empty accumulator and modulus.
func NewWorkspace() *Workspace {
	return &Workspace{}
}

// Gcd returns the greatest common divisor of two uint64 values.
func Gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// AccessStepU64 applies one residue step r -> (q*r + c) mod D. The caller must
// keep q*D + c below 2^58, which the sweep bounds guarantee.
func AccessStepU64(q, c, D, r uint64) uint64 {
	return (q*r + c) % D
}

// AccessModulusU64 computes D*(q-1)/gcd(c, D*(q-1)), the modulus whose
// multiplicative order of q is the return time of the residue orbit of zero.
func AccessModulusU64(q, c, D uint64) uint64 {
	top := D * (q - 1)
	return top / Gcd(c, top)
}

// AccessOrbitU64 walks the residue orbit of zero for j steps.
func AccessOrbitU64(q, c, D, j uint64) uint64 {
	r := uint64(0)
	for i := uint64(0); i < j; i++ {
		r = AccessStepU64(q, c, D, r)
	}
	return r
}

// RepunitSumBig returns 1 + q + ... + q^(j-1) in w, so the caller can compare
// the reduced orbit with the exact affine offset c*(1 + q + ... + q^(j-1)).
func RepunitSumBig(w *Workspace, q uint64, j uint64) *big.Int {
	w.Base.SetUint64(q)
	w.Acc.SetInt64(0)
	w.Pow.SetInt64(1)
	for i := uint64(0); i < j; i++ {
		w.Acc.Add(&w.Acc, &w.Pow)
		w.Pow.Mul(&w.Pow, &w.Base)
	}
	return &w.Acc
}

// ModulusByPowers computes the access modulus by reducing q^j - 1 modulo
// D*(q-1) step by step, an independent route to AccessModulusU64.
func ModulusByPowers(q, c, D uint64) uint64 {
	top := D * (q - 1)
	return top / Gcd(c, top)
}

// LeastOrderBig returns the least m with 1 <= m <= cap such that q^m is one
// modulo M, together with a flag reporting whether such an m exists. The
// search multiplies step by step modulo M, so no value ever exceeds M^2.
func LeastOrderBig(w *Workspace, q, M, cap uint64) (uint64, bool) {
	if M == 1 {
		return 1, true
	}
	w.Acc.SetInt64(1)
	w.Base.SetUint64(q)
	w.Mod.SetUint64(M)
	w.Pow.SetUint64(q % M)
	for m := uint64(1); m <= cap; m++ {
		if w.Pow.Cmp(&w.Acc) == 0 {
			return m, true
		}
		w.Pow.Mul(&w.Pow, &w.Base)
		w.Pow.Mod(&w.Pow, &w.Mod)
	}
	return 0, false
}

// dividesBig reports whether M divides n, which the criterion uses on q^j - 1.
func dividesBig(w *Workspace, n *big.Int, M uint64) bool {
	w.Mod.SetUint64(M)
	w.Pow.Mod(n, &w.Mod)
	return w.Pow.Sign() == 0
}

// PowSubOneBig writes q^j - 1 into w and returns it.
func PowSubOneBig(w *Workspace, q, j uint64) *big.Int {
	w.Base.SetUint64(q)
	w.Exp.SetUint64(j)
	w.Pow.Exp(&w.Base, &w.Exp, nil)
	w.Pow.Sub(&w.Pow, bigOne)
	return &w.Pow
}

// OrbitSetU64 returns the set of residues visited by the orbit of zero within
// m steps, as a slice of flags indexed by residue.
func OrbitSetU64(q, c, D, m uint64) []bool {
	seen := make([]bool, D)
	r := uint64(0)
	for i := uint64(0); i < m; i++ {
		seen[r] = true
		r = AccessStepU64(q, c, D, r)
	}
	return seen
}

// sweepFormula checks AccessOrbit j = (c * RepunitSum q j) mod D on the
// bounded rectangle, comparing the walking orbit with the closed form.
func sweepFormula() Totals {
	var t Totals
	w := NewWorkspace()
	for q := uint64(2); q <= accessMaxQ; q++ {
		for c := uint64(1); c <= accessMaxC; c++ {
			for D := uint64(2); D <= accessMaxD; D++ {
				for j := uint64(0); j <= accessMaxJ; j++ {
					closed := RepunitSumBig(w, q, j)
					closed.Mul(closed, new(big.Int).SetUint64(c))
					closed.Mod(closed, new(big.Int).SetUint64(D))
					t.check(closed.Uint64() == AccessOrbitU64(q, c, D, j))
				}
			}
		}
	}
	return t
}

// sweepCriterion checks AccessOrbit j = 0 iff the access modulus divides
// q^j - 1 on the bounded rectangle.
func sweepCriterion() Totals {
	var t Totals
	w := NewWorkspace()
	for q := uint64(2); q <= accessMaxQ; q++ {
		for c := uint64(1); c <= accessMaxC; c++ {
			for D := uint64(2); D <= accessMaxD; D++ {
				M := AccessModulusU64(q, c, D)
				for j := uint64(1); j <= accessMaxJ; j++ {
					zero := AccessOrbitU64(q, c, D, j) == 0
					divides := dividesBig(w, PowSubOneBig(w, q, j), M)
					t.check(zero == divides)
				}
			}
		}
	}
	return t
}

// sweepOrder checks that on coprime pairs the return time of the orbit is the
// least exponent with q^m = 1 modulo the access modulus, and that m <= D.
func sweepOrder() Totals {
	var t Totals
	w := NewWorkspace()
	for q := uint64(2); q <= accessMaxQ; q++ {
		for c := uint64(1); c <= accessMaxC; c++ {
			for D := uint64(2); D <= accessMaxD; D++ {
				if Gcd(q, D) != 1 {
					continue
				}
				M := ModulusByPowers(q, c, D)
				m, found := LeastOrderBig(w, q, M, accessOrderCap)
				if !found {
					t.check(false)
					continue
				}
				t.check(m <= D)
				t.check(AccessOrbitU64(q, c, D, m) == 0)
				for s := uint64(1); s < m; s++ {
					t.check(AccessOrbitU64(q, c, D, s) != 0)
				}
				for j := uint64(1); j <= accessMaxJ; j++ {
					t.check((AccessOrbitU64(q, c, D, j) == 0) == (j%m == 0))
				}
			}
		}
	}
	return t
}

// sweepFullAccess checks the prime case where the multiplier is one modulo the
// prime: the return time is the prime and the orbit exhausts the residues.
func sweepFullAccess() Totals {
	var t Totals
	w := NewWorkspace()
	primes := []uint64{2, 3, 5, 7, 11, 13}
	for _, p := range primes {
		for q := uint64(2); q <= accessPrimeQ; q++ {
			if Gcd(q, p) != 1 || (q-1)%p != 0 {
				continue
			}
			for c := uint64(1); c < p; c++ {
				M := AccessModulusU64(q, c, p)
				m, found := LeastOrderBig(w, q, M, accessOrderCap)
				t.check(found && m == p)
				seen := OrbitSetU64(q, c, p, p)
				for r := uint64(0); r < p; r++ {
					t.check(seen[r])
				}
			}
		}
	}
	return t
}

// sweepPrimeNonOne checks the prime case where the multiplier is not one: the
// return time is smaller than the prime, so some residue is unreachable.
func sweepPrimeNonOne() Totals {
	var t Totals
	w := NewWorkspace()
	primes := []uint64{2, 3, 5, 7, 11, 13}
	for _, p := range primes {
		for q := uint64(2); q <= accessPrimeQ; q++ {
			if Gcd(q, p) != 1 || (q-1)%p == 0 {
				continue
			}
			for c := uint64(1); c < p; c++ {
				M := AccessModulusU64(q, c, p)
				m, found := LeastOrderBig(w, q, M, accessOrderCap)
				t.check(found && m < p)
				seen := OrbitSetU64(q, c, p, m)
				unreached := uint64(0)
				for r := uint64(0); r < p; r++ {
					if !seen[r] {
						unreached++
					}
				}
				t.check(unreached == p-m)
			}
		}
	}
	return t
}

// sweepExamples checks the worked examples of the source section, including
// the trap residue modulo three and the two-cycle case with a non-area
// multiplier.
func sweepExamples() Totals {
	var t Totals
	w := NewWorkspace()
	// (2,1,3): return time two, accessible residues 0 and 1, trap residue 2.
	t.check(AccessOrbitU64(2, 1, 3, 0) == 0 && AccessOrbitU64(2, 1, 3, 1) == 1)
	t.check(AccessOrbitU64(2, 1, 3, 2) == 0 && AccessOrbitU64(2, 1, 3, 3) == 1)
	t.check(AccessStepU64(2, 1, 3, 2) == 2)
	// (2,1,7): return time three with accessible residues 0, 1 and 3.
	t.check(AccessOrbitU64(2, 1, 7, 1) == 1 && AccessOrbitU64(2, 1, 7, 2) == 3)
	t.check(AccessOrbitU64(2, 1, 7, 3) == 0)
	// (2,1,15): return time four.
	t.check(AccessOrbitU64(2, 1, 15, 1) == 1 && AccessOrbitU64(2, 1, 15, 2) == 3)
	t.check(AccessOrbitU64(2, 1, 15, 3) == 7 && AccessOrbitU64(2, 1, 15, 4) == 0)
	// (3,1,13): return time three.
	t.check(AccessOrbitU64(3, 1, 13, 1) == 1 && AccessOrbitU64(3, 1, 13, 2) == 4)
	t.check(AccessOrbitU64(3, 1, 13, 3) == 0)
	// (3,1,2): full access modulo two, return time two.
	t.check(AccessOrbitU64(3, 1, 2, 1) == 1 && AccessOrbitU64(3, 1, 2, 2) == 0)
	// (2,7,3): return time two with the two-cycle of residues zero and one.
	t.check(AccessOrbitU64(2, 7, 3, 1) == 1 && AccessOrbitU64(2, 7, 3, 2) == 0)
	// Every multiplier q = D - 1 with c not divisible by D has return time two.
	for D := uint64(3); D <= 13; D++ {
		for c := uint64(1); c < D; c++ {
			M := AccessModulusU64(D-1, c, D)
			m, found := LeastOrderBig(w, D-1, M, accessOrderCap)
			t.check(found && m == 2)
		}
	}
	return t
}

// parallelAccessSweep runs one per-multiplier sweep over chunked workers and
// merges the totals.
func parallelAccessSweep(fn func(w *Workspace, q, c, D, j uint64) bool) Totals {
	qs := make([]uint64, 0, accessMaxQ)
	for q := uint64(2); q <= accessMaxQ; q++ {
		qs = append(qs, q)
	}
	chunks := make([][]uint64, accessWorkers)
	for i, q := range qs {
		chunks[i%accessWorkers] = append(chunks[i%accessWorkers], q)
	}
	partial := make([]Totals, accessWorkers)
	var wg sync.WaitGroup
	for i := range chunks {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			var t Totals
			w := NewWorkspace()
			for _, q := range chunks[i] {
				for c := uint64(1); c <= accessMaxC; c++ {
					for D := uint64(2); D <= accessMaxD; D++ {
						for j := uint64(0); j <= accessMaxJ; j++ {
							t.check(fn(w, q, c, D, j))
						}
					}
				}
			}
			partial[i] = t
		}(i)
	}
	wg.Wait()
	var total Totals
	for _, t := range partial {
		total.Checks += t.Checks
		total.Failures += t.Failures
	}
	return total
}

// main runs every sweep, prints the per-slice totals and exits nonzero when a
// single check fails.
func main() {
	var run Totals
	formula := parallelAccessSweep(func(w *Workspace, q, c, D, j uint64) bool {
		closed := RepunitSumBig(w, q, j)
		w.Exp.SetUint64(c)
		closed.Mul(closed, &w.Exp)
		w.Exp.SetUint64(D)
		closed.Mod(closed, &w.Exp)
		return closed.Uint64() == AccessOrbitU64(q, c, D, j)
	})
	run.Checks += formula.Checks
	run.Failures += formula.Failures
	fmt.Printf("orbit formula: %d, failures: %d\n", formula.Checks, formula.Failures)

	criterion := sweepCriterion()
	run.Checks += criterion.Checks
	run.Failures += criterion.Failures
	fmt.Printf("modulus criterion: %d, failures: %d\n", criterion.Checks, criterion.Failures)

	order := sweepOrder()
	run.Checks += order.Checks
	run.Failures += order.Failures
	fmt.Printf("order and period: %d, failures: %d\n", order.Checks, order.Failures)

	full := sweepFullAccess()
	run.Checks += full.Checks
	run.Failures += full.Failures
	fmt.Printf("prime full access: %d, failures: %d\n", full.Checks, full.Failures)

	nonone := sweepPrimeNonOne()
	run.Checks += nonone.Checks
	run.Failures += nonone.Failures
	fmt.Printf("prime non-one: %d, failures: %d\n", nonone.Checks, nonone.Failures)

	examples := sweepExamples()
	run.Checks += examples.Checks
	run.Failures += examples.Failures
	fmt.Printf("worked examples: %d, failures: %d\n", examples.Checks, examples.Failures)

	fmt.Printf("residue access checks: %d, failures: %d\n", run.Checks, run.Failures)
	if run.Failures != 0 {
		os.Exit(1)
	}
}
