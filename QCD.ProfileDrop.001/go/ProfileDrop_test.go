// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math"
	"math/big"
	"testing"
)

// Cache reuses exact arithmetic and a six-state reference graph between test rows.
type Cache struct {
	Values [8]big.Int
	Next   [6]int64
	Dies   [6]bool
}

// ReferenceInt64 refuses to narrow an exact value that the machine type cannot hold.
func ReferenceInt64(v *big.Int) int64 {
	if !v.IsInt64() {
		panic("exact reference outside int64")
	}
	return v.Int64()
}

// ReferenceAffine evaluates the affine branch with independent arbitrary precision.
func ReferenceAffine(cache *Cache, q, c, n int64) int64 {
	v := cache.Values[:len(cache.Values)]
	v[0].SetInt64(q)
	v[1].SetInt64(n)
	v[2].SetInt64(c)
	v[0].Mul(&v[0], &v[1])
	v[0].Add(&v[0], &v[2])
	return ReferenceInt64(&v[0])
}

// ReferenceDisplacement computes the subtraction and products without machine arithmetic.
func ReferenceDisplacement(cache *Cache, q, c, n int64) int64 {
	v := cache.Values[:len(cache.Values)]
	v[0].SetInt64(q)
	v[1].SetInt64(1)
	v[2].SetInt64(n)
	v[3].SetInt64(c)
	v[0].Sub(&v[0], &v[1])
	v[0].Mul(&v[0], &v[2])
	v[0].Add(&v[0], &v[3])
	return ReferenceInt64(&v[0])
}

// ReferenceProduct evaluates the multiplier recurrence in arbitrary precision.
func ReferenceProduct(cache *Cache, q, z int64) int64 {
	v := cache.Values[:len(cache.Values)]
	v[0].SetInt64(q)
	v[1].SetInt64(z)
	v[0].Mul(&v[0], &v[1])
	return ReferenceInt64(&v[0])
}

// ReferenceModulo uses Euclidean big.Int.Mod rather than the production remainder repair.
func ReferenceModulo(cache *Cache, n, m int64) int64 {
	v := cache.Values[:len(cache.Values)]
	v[0].SetInt64(n)
	v[1].SetInt64(m)
	v[0].Mod(&v[0], &v[1])
	return ReferenceInt64(&v[0])
}

// ReferenceGraph deletes zero and its predecessors instead of scanning a visited bitmask.
// After m rounds, a remaining nonzero state has a zero-avoiding forward path.
func ReferenceGraph(cache *Cache, q, c, m int64) bool {
	cache.Dies = [6]bool{}
	cache.Dies[0] = true
	for r := int64(0); r < m; r++ {
		next := ReferenceAffine(cache, q, c, r)
		cache.Next[r] = ReferenceModulo(cache, next, m)
	}
	for round := int64(0); round < m; round++ {
		for r := int64(1); r < m; r++ {
			if cache.Dies[cache.Next[r]] {
				cache.Dies[r] = true
			}
		}
	}
	for r := int64(1); r < m; r++ {
		if !cache.Dies[r] {
			return true
		}
	}
	return false
}

// ReferenceCycleLength checks closure at the returned residue using the exact graph.
func ReferenceCycleLength(cache *Cache, m, start int64) int64 {
	if start <= 0 || start >= m {
		return 0
	}
	r := start
	for p := int64(1); p < m; p++ {
		r = cache.Next[r]
		if r == 0 {
			return 0
		}
		if r == start {
			return p
		}
	}
	return 0
}

// TestKnownCycles checks a fixed point, a two-cycle, and a graph absorbed by zero.
func TestKnownCycles(t *testing.T) {
	r, found := HasZeroAvoidingCycle(2, 1, 3)
	if !found || r != 2 || CycleLength(2, 1, 3, r) != 1 {
		t.Fatalf("fixed point: residue=%d found=%t", r, found)
	}
	r, found = HasZeroAvoidingCycle(2, 0, 3)
	if !found || CycleLength(2, 0, 3, r) != 2 {
		t.Fatalf("two-cycle: residue=%d found=%t", r, found)
	}
	if _, found = HasZeroAvoidingCycle(2, 0, 2); found {
		t.Fatal("doubling modulo two was reported as zero-avoiding")
	}
	if !ReachesZero(2, 0, 2, 0) || !ReachesZero(2, 0, 2, 1) {
		t.Fatal("a state modulo two did not reach zero")
	}
	r, found = HasZeroAvoidingCycle(-3, 2, 5)
	if !found || r != 3 || CycleLength(-3, 2, 5, r) != 1 {
		t.Fatalf("negative multiplier fixed point: residue=%d found=%t", r, found)
	}
}

// TestComputedExamples checks the displayed closed forms against exact stepped orbits.
func TestComputedExamples(t *testing.T) {
	var cache Cache
	states := [4]int64{5, 4, 8, 5}
	multipliers := [4]int64{2, 2, -3, 2}
	offsets := [4]int64{1, 0, 2, -3}
	moduli := [4]int64{3, 3, 5, 2}
	powerTwo, powerNegThree := int64(1), int64(1)
	for step := 0; step <= OrbitSteps; step++ {
		// The formula products have magnitude at most 15*3^8+1 < 2^17.
		want := [4]int64{6*powerTwo - 1, 4 * powerTwo,
			(15*powerNegThree + 1) / 2, 3 + 2*powerTwo}
		for row := range states {
			if states[row] != want[row] ||
				ReferenceModulo(&cache, states[row], moduli[row]) == 0 {
				t.Fatalf("closed form row=%d step=%d got=%d want=%d",
					row, step, states[row], want[row])
			}
			if step < OrbitSteps {
				next := ReferenceAffine(&cache, multipliers[row], offsets[row], states[row])
				if Affine(multipliers[row], offsets[row], states[row]) != next {
					t.Fatal("computed example disagreed with exact arithmetic")
				}
				states[row] = next
			}
		}
		powerTwo *= 2
		powerNegThree *= -3
	}
	if ReferenceAffine(&cache, 2, -3, 3) != 3 || Displacement(2, -3, 3) != 0 {
		t.Fatal("the zero-displacement exception was not an affine fixed point")
	}
}

// TestGridIdentitiesAgainstExactReference checks every seed, including negative seeds.
func TestGridIdentitiesAgainstExactReference(t *testing.T) {
	var cache Cache
	rows := 0
	for q := GridQMin; q <= GridQMax; q++ {
		if -2 < q && q < 2 {
			continue
		}
		for c := GridCMin; c <= GridCMax; c++ {
			for n := GridNMin; n <= GridNMax; n++ {
				once := ReferenceAffine(&cache, q, c, n)
				twice := ReferenceAffine(&cache, q, c, once)
				z := ReferenceDisplacement(&cache, q, c, n)
				zOnce := ReferenceDisplacement(&cache, q, c, once)
				zTwice := ReferenceDisplacement(&cache, q, c, twice)
				if Affine(q, c, n) != once || Displacement(q, c, n) != z ||
					zOnce != ReferenceProduct(&cache, q, z) ||
					zTwice != ReferenceProduct(&cache, q, zOnce) ||
					!DisplacementIdentity(q, c, n) || !TwoStepIdentity(q, c, n) {
					t.Fatalf("affine reference mismatch q=%d c=%d n=%d", q, c, n)
				}
				for m := GridMMin; m <= GridMMax; m++ {
					r := ReferenceModulo(&cache, n, m)
					next := ReferenceAffine(&cache, q, c, r)
					want := ReferenceModulo(&cache, next, m)
					if EuclideanMod(n, m) != r || EuclideanMod(once, m) != want ||
						!ResidueIdentity(q, c, n, m) {
						t.Fatalf("residue reference mismatch q=%d c=%d m=%d n=%d",
							q, c, m, n)
					}
				}
				rows++
			}
		}
	}
	if rows != 8*11*17 {
		t.Fatalf("seed rectangle rows=%d", rows)
	}
}

// TestPositiveLiftsAgainstExactReference checks both candidates for every grid residue.
func TestPositiveLiftsAgainstExactReference(t *testing.T) {
	var cache Cache
	for q := GridQMin; q <= GridQMax; q++ {
		if -2 < q && q < 2 {
			continue
		}
		for c := GridCMin; c <= GridCMax; c++ {
			for m := GridMMin; m <= GridMMax; m++ {
				for r := int64(0); r < m; r++ {
					want := r + m
					if ReferenceDisplacement(&cache, q, c, want) == 0 {
						want = r + 2*m
					}
					seed, ok := PositiveLift(q, c, m, r)
					if !ok || seed != want || seed <= 0 || seed > 17 ||
						ReferenceModulo(&cache, seed, m) != r ||
						ReferenceDisplacement(&cache, q, c, seed) == 0 {
						t.Fatalf("lift mismatch q=%d c=%d m=%d r=%d seed=%d",
							q, c, m, r, seed)
					}
				}
			}
		}
	}
	seed, ok := PositiveLift(2, -3, 2, 1)
	if !ok || seed != 5 {
		t.Fatalf("second lift was not selected: seed=%d ok=%t", seed, ok)
	}
}

// CheckLiftedOrbit compares every visited state with exact arithmetic and the exact graph.
func CheckLiftedOrbit(t *testing.T, cache *Cache, q, c, m, cycle int64) {
	seed, ok := PositiveLift(q, c, m, cycle)
	if !ok {
		t.Fatal("cycle residue did not lift")
	}
	state := seed
	r := cycle
	v := cache.Values[:len(cache.Values)]
	v[4].SetInt64(ReferenceDisplacement(cache, q, c, seed))
	v[5].SetInt64(q)
	v[7].SetInt64(seed)
	for step := 0; step <= OrbitSteps; step++ {
		z := ReferenceDisplacement(cache, q, c, state)
		v[6].SetInt64(state)
		v[6].Abs(&v[6])
		if !v[6].IsInt64() || v[6].Int64() > OrbitStateBound ||
			z != ReferenceInt64(&v[4]) || Displacement(q, c, state) != z ||
			r == 0 || ReferenceModulo(cache, state, m) != r ||
			Divides(m, state) || Divides(-m, state) {
			t.Fatalf("orbit mismatch q=%d c=%d m=%d seed=%d step=%d state=%d",
				q, c, m, seed, step, state)
		}
		if step == OrbitSteps {
			if v[6].Cmp(&v[7]) <= 0 {
				t.Fatal("terminal magnitude did not exceed the positive seed")
			}
			break
		}
		next := ReferenceAffine(cache, q, c, state)
		if Affine(q, c, state) != next {
			t.Fatal("lifted affine step disagreed with exact arithmetic")
		}
		state = next
		r = cache.Next[r]
		v[4].Mul(&v[4], &v[5])
	}
}

// TestFiniteCyclesAgainstExactGraph audits existence, returned witnesses, and lifted paths.
func TestFiniteCyclesAgainstExactGraph(t *testing.T) {
	var cache Cache
	var foundCases uint64
	rows := 0
	for q := GridQMin; q <= GridQMax; q++ {
		if -2 < q && q < 2 {
			continue
		}
		for c := GridCMin; c <= GridCMax; c++ {
			for m := GridMMin; m <= GridMMax; m++ {
				want := ReferenceGraph(&cache, q, c, m)
				cycle, found := HasZeroAvoidingCycle(q, c, m)
				if found != want {
					t.Fatalf("cycle existence mismatch q=%d c=%d m=%d", q, c, m)
				}
				for r := int64(0); r < m; r++ {
					if ReachesZero(q, c, m, r) != cache.Dies[r] {
						t.Fatalf("zero-reaching mismatch q=%d c=%d m=%d r=%d", q, c, m, r)
					}
				}
				if found {
					period := ReferenceCycleLength(&cache, m, cycle)
					if period == 0 || CycleLength(q, c, m, cycle) != period {
						t.Fatalf("returned residue is not a cycle state: %d", cycle)
					}
					CheckLiftedOrbit(t, &cache, q, c, m, cycle)
					foundCases++
				} else if cycle != 0 {
					t.Fatal("absent cycle returned a nonzero witness")
				}
				rows++
			}
		}
	}
	w := CheckGrid(EqualReports)
	if rows != 440 || w.CycleCases != foundCases ||
		w.Checks != 11118+39*foundCases || w.Failures != 0 {
		t.Fatalf("certificate coverage: rows=%d exact cycles=%d result=%+v",
			rows, foundCases, w)
	}
}

// TestSignedDivisorsAgainstExactReference checks sign-invariance against big.Int.Mod.
func TestSignedDivisorsAgainstExactReference(t *testing.T) {
	var cache Cache
	for d := GridMMin; d <= GridMMax; d++ {
		for n := int64(-20); n <= 20; n++ {
			want := ReferenceModulo(&cache, n, d) == 0
			if Divides(d, n) != want || Divides(-d, n) != want ||
				!SameDivisorSign(d, n) {
				t.Fatalf("signed divisibility mismatch d=%d n=%d", d, n)
			}
		}
	}
}

// TestGridRejectsNonSeparatingPredicates exercises the actual certificate entry point.
func TestGridRejectsNonSeparatingPredicates(t *testing.T) {
	shifted := func(got, want int64) bool { return got == want+1 }
	constantFalse := func(got, want int64) bool { return false }
	good := CheckGrid(EqualReports)
	for _, pred := range []func(int64, int64) bool{ConstantTrue, constantFalse, shifted} {
		bad := CheckGrid(pred)
		if bad.Failures == 0 || bad.Checks != good.Checks ||
			bad.CycleCases != good.CycleCases {
			t.Fatalf("negative control accepted or skipped rows: %+v", bad)
		}
	}
	if CheckGrid(ConstantTrue).Failures != 1 {
		t.Fatal("constant true did not fail exactly the separating-predicate check")
	}
}

// ExpectPanic distinguishes an explicitly rejected input from a silently accepted one.
func ExpectPanic(t *testing.T, call func()) {
	t.Helper()
	defer func() {
		if recover() == nil {
			t.Fatal("unsupported input was not rejected")
		}
	}()
	call()
}

// TestUnsupportedInputsRejected covers bit-width, zero division, and overflow boundaries.
func TestUnsupportedInputsRejected(t *testing.T) {
	cases := []struct {
		Name string
		Call func()
	}{
		{"zero-modulus", func() { EuclideanMod(1, 0) }},
		{"negative-modulus", func() { EuclideanMod(1, -2) }},
		{"unit-modulus", func() { HasZeroAvoidingCycle(2, 1, 1) }},
		{"mask-width", func() { HasZeroAvoidingCycle(2, 1, 65) }},
		{"large-modulus", func() { HasZeroAvoidingCycle(2, 1, math.MaxInt64) }},
		{"large-multiplier", func() { Affine(math.MaxInt64, 1, 1) }},
		{"excluded-multiplier", func() { PositiveLift(1, 1, 2, 1) }},
		{"large-offset", func() { Displacement(2, math.MaxInt64, 1) }},
		{"minimal-operand", func() { AbsInt(math.MinInt64) }},
		{"large-operand", func() { Affine(2, 1, math.MaxInt64) }},
		{"zero-divisor", func() { Divides(0, 1) }},
		{"minimal-divisor", func() { SameDivisorSign(math.MinInt64, 1) }},
		{"invalid-residue", func() { PositiveLift(2, 1, 3, 3) }},
		{"negative-residue", func() { ReachesZero(2, 1, 3, -1) }},
		{"large-seed", func() { TwoStepIdentity(2, 1, math.MaxInt64) }},
		{"nil-predicate", func() { CheckGrid(nil) }},
	}
	for _, row := range cases {
		t.Run(row.Name, func(t *testing.T) { ExpectPanic(t, row.Call) })
	}
}

// TestParallelAgreement checks the disjoint-worker reduction on repeated launches.
func TestParallelAgreement(t *testing.T) {
	want := CheckGrid(EqualReports)
	for run := 0; run < 16; run++ {
		if got := CheckGridParallel(EqualReports); got != want {
			t.Fatalf("parallel result=%+v sequential result=%+v", got, want)
		}
	}
	if got := CheckGridParallel(ConstantTrue); got.Failures != 1 {
		t.Fatalf("parallel negative control result=%+v", got)
	}
}

// TestSequentialCertificateAllocations excludes heap allocation in the checking loops.
func TestSequentialCertificateAllocations(t *testing.T) {
	var w Workspace
	allocations := testing.AllocsPerRun(20, func() { w = CheckGrid(EqualReports) })
	if allocations != 0 || w.Failures != 0 {
		t.Fatalf("allocations=%g certificate=%+v", allocations, w)
	}
}
