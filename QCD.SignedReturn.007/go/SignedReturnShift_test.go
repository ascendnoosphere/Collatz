// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// BigAffine evaluates q^j*n + c*T_j(q) with arbitrary-precision arithmetic.
func BigAffine(q, c, n int64, j int) *big.Int {
	pow := big.NewInt(1)
	trap := big.NewInt(0)
	qb := big.NewInt(q)
	for i := 0; i < j; i++ {
		trap.Add(trap, pow)
		pow.Mul(pow, qb)
	}
	term := new(big.Int).Mul(pow, big.NewInt(n))
	off := new(big.Int).Mul(big.NewInt(c), trap)
	return term.Add(term, off)
}

// Int64Exact converts a big integer that is known to fit in an int64.
func Int64Exact(t *testing.T, z *big.Int) int64 {
	t.Helper()
	if !z.IsInt64() {
		t.Fatalf("value %s does not fit in int64", z.String())
	}
	return z.Int64()
}

// TestIncrementRejectsUnitSlack fails if the shift predicate is replaced by true.
func TestIncrementRejectsUnitSlack(t *testing.T) {
	w := NewWorkspace()
	// q = -2, j = 3, c = 3, n = 4, t = -3, d = -5.
	// q^j = -8, T_j(q) = 3, and q^j*t*d = -120.
	w.Prepare(-2, 3)
	if w.Pow != -8 || w.Trap != 3 {
		t.Fatalf("prepared power %d sum %d", w.Pow, w.Trap)
	}
	claimed := w.Pow * (-3) * (-5)
	if claimed != -120 {
		t.Fatalf("claimed shift %d", claimed)
	}
	if !IncrementIs(w.Pow, w.Trap, 3, 4, -3, -5, claimed) {
		t.Fatal("negative shift disagreed with q^j*t*d")
	}
	if IncrementIs(w.Pow, w.Trap, 3, 4, -3, -5, claimed+1) {
		t.Fatal("unit slack was accepted")
	}
}

// TestNegativeShiftMatchesBig checks corners, including negative t and d.
func TestNegativeShiftMatchesBig(t *testing.T) {
	w := NewWorkspace()
	ns := []int64{shiftNMin, shiftNMax}
	cs := []int64{shiftCMin, shiftCMax}
	ts := []int64{shiftTMin, shiftTMax}
	ds := []int64{shiftDMin, -1, 0, 1, shiftDMax}
	for q := int64(shiftQMin); q <= shiftQMax; q++ {
		for j := 0; j <= shiftJMax; j++ {
			w.Prepare(q, j)
			for _, c := range cs {
				for _, n := range ns {
					for _, tv := range ts {
						for _, d := range ds {
							got := AffineValue(w.Pow, w.Trap, c, n+tv*d)
							want := Int64Exact(t, BigAffine(q, c, n+tv*d, j))
							if got != want {
								t.Fatalf("state mismatch q=%d c=%d n=%d t=%d d=%d j=%d",
									q, c, n, tv, d, j)
							}
							diff := got - AffineValue(w.Pow, w.Trap, c, n)
							claimed := Int64Exact(t, new(big.Int).Mul(
								new(big.Int).Mul(big.NewInt(w.Pow), big.NewInt(tv)),
								big.NewInt(d)))
							if diff != claimed {
								t.Fatalf("difference mismatch q=%d j=%d", q, j)
							}
							if !IncrementIs(w.Pow, w.Trap, c, n, tv, d, claimed) {
								t.Fatalf("predicate rejected a true shift q=%d j=%d", q, j)
							}
						}
					}
				}
			}
		}
	}
}

// TestDividesSigned checks negative divisors and the zero divisor.
func TestDividesSigned(t *testing.T) {
	if !Divides(-3, 6) || !Divides(-3, -6) || !Divides(3, -6) {
		t.Fatal("a genuine multiple was rejected")
	}
	if Divides(-3, 1) || Divides(2, -1) || Divides(0, 5) {
		t.Fatal("a non-multiple was accepted")
	}
	if !Divides(0, 0) || !Divides(-2, 0) {
		t.Fatal("zero is a multiple of every integer")
	}
}

// TestFirstHitWitnesses checks a hit, a miss, an earlier hit, and transport.
func TestFirstHitWitnesses(t *testing.T) {
	cache := NewCache()
	cache.Load(1)
	// Affine state of q = 1, c = 0 is the seed at every time.
	if IsFirstHit(cache, 0, 2, 1, 0) {
		t.Fatal("2 does not divide 1")
	}
	if !IsFirstHit(cache, 0, 2, 2, 0) {
		t.Fatal("time zero is a first hit of the even seed")
	}
	if IsFirstHit(cache, 0, 2, 2, 1) {
		t.Fatal("an earlier hit was ignored")
	}
	// n = 2 and n+(-1)*2 = 0 have the same first-hit pattern.
	if !IsFirstHit(cache, 0, 2, 0, 0) {
		t.Fatal("2 divides 0 at time zero")
	}
	if IsFirstHit(cache, 0, 2, 0, 1) {
		t.Fatal("shifted seed kept a later time as first")
	}
	cache.Load(-1)
	// At j = 1 the state is -n+c. For c = 1 and n = 1 this is 0.
	if !IsFirstHit(cache, 1, 3, 1, 1) {
		t.Fatal("expected a first hit at time one")
	}
	if IsFirstHit(cache, 1, 3, 1, 0) {
		t.Fatal("3 does not divide the seed 1")
	}
	// Shift by one divisor: n = 4. The time-one state is -4+1 = -3.
	if !IsFirstHit(cache, 1, 3, 4, 1) {
		t.Fatal("shifted seed lost the first hit")
	}
	if IsFirstHit(cache, 1, -3, 1, 0) {
		t.Fatal("negative divisor divided a non-multiple")
	}
	if !IsFirstHit(cache, 0, -3, 3, 0) {
		t.Fatal("negative divisor rejected a multiple at time zero")
	}
}

// TestFirstHitNotConstant fails if IsFirstHit is replaced by true or by false.
func TestFirstHitNotConstant(t *testing.T) {
	hits := RunHitSweep()
	if hits.Failures != 0 {
		t.Fatalf("first-hit transport failures %d", hits.Failures)
	}
	if hits.Hits == 0 || hits.Hits == hits.Checks {
		t.Fatalf("first-hit predicate is constant: hits %d checks %d",
			hits.Hits, hits.Checks)
	}
	if hits.Checks != HitDomainSize() {
		t.Fatalf("hit checks %d domain %d", hits.Checks, HitDomainSize())
	}
}

// TestIdentityDomainAndSweep pins the grid size and demands zero disagreements.
func TestIdentityDomainAndSweep(t *testing.T) {
	qCount := uint64(shiftQMax - shiftQMin + 1)
	jCount := uint64(shiftJMax + 1)
	cCount := uint64(shiftCMax - shiftCMin + 1)
	nCount := uint64(shiftNMax - shiftNMin + 1)
	tCount := uint64(shiftTMax - shiftTMin + 1)
	dCount := uint64(shiftDMax - shiftDMin + 1)
	product := qCount * jCount * cCount * nCount * tCount * dCount
	if product != 586971 {
		t.Fatalf("identity product %d", product)
	}
	if IdentityDomainSize() != product {
		t.Fatalf("identity domain %d product %d", IdentityDomainSize(), product)
	}
	got := RunIdentitySweep()
	if got.Checks != product || got.Failures != 0 {
		t.Fatalf("identity checks %d failures %d", got.Checks, got.Failures)
	}
	hq := uint64(hitQMax - hitQMin + 1)
	hj := uint64(hitJMax + 1)
	hc := uint64(hitCMax - hitCMin + 1)
	hn := uint64(hitNMax - hitNMin + 1)
	ht := uint64(hitTMax - hitTMin + 1)
	hitProduct := hq * hj * hc * hn * ht * 6
	if hitProduct != 95550 {
		t.Fatalf("hit product %d", hitProduct)
	}
	if HitDomainSize() != hitProduct {
		t.Fatalf("hit domain %d product %d", HitDomainSize(), hitProduct)
	}
}

// TestPrepareAllocatesNothing checks that a warm power update does not allocate.
func TestPrepareAllocatesNothing(t *testing.T) {
	w := NewWorkspace()
	w.Prepare(3, shiftJMax)
	allocs := testing.AllocsPerRun(100, func() {
		w.Prepare(-3, shiftJMax)
		if !IncrementIs(w.Pow, w.Trap, -4, -5, -5, -5, w.Pow*(-5)*(-5)) {
			panic("shift failed inside the allocation probe")
		}
	})
	if allocs != 0 {
		t.Fatalf("prepare allocated %v times per run", allocs)
	}
}
