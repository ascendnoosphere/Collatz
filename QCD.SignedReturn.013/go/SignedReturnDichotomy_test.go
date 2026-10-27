// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"math/big"
	"testing"
)

// BigOffset returns U_j(q) from the closed form (q^j-1)/(q-1), with the
// two degenerate cases U_0(q) = 0 and U_j(1) = j. The quotient is exact.
func BigOffset(q int64, j int) *big.Int {
	if j == 0 {
		return big.NewInt(0)
	}
	if q == 1 {
		return big.NewInt(int64(j))
	}
	pow := new(big.Int).Exp(big.NewInt(q), big.NewInt(int64(j)), nil)
	num := new(big.Int).Sub(pow, big.NewInt(1))
	return num.Quo(num, big.NewInt(q-1))
}

// BigAffine returns q^j*n + c*U_j(q) with big-integer arithmetic.
func BigAffine(q, c int64, j int, n int64) *big.Int {
	pow := new(big.Int).Exp(big.NewInt(q), big.NewInt(int64(j)), nil)
	term := new(big.Int).Mul(pow, big.NewInt(n))
	offset := new(big.Int).Mul(big.NewInt(c), BigOffset(q, j))
	return term.Add(term, offset)
}

// BigStep applies one raw step with big-integer truncation toward zero.
func BigStep(q, c, D int64, n *big.Int) *big.Int {
	bigD := big.NewInt(D)
	if new(big.Int).Rem(n, bigD).Sign() == 0 {
		return new(big.Int).Quo(n, bigD)
	}
	out := new(big.Int).Mul(big.NewInt(q), new(big.Int).Set(n))
	return out.Add(out, big.NewInt(c))
}

// BigRaw returns the raw state at time j.
func BigRaw(q, c, D, n int64, j int) *big.Int {
	cur := big.NewInt(n)
	for i := 0; i < j; i++ {
		cur = BigStep(q, c, D, cur)
	}
	return cur
}

// BigDivides reports whether D divides n. The remainder sign is irrelevant:
// only the zero remainder is accepted.
func BigDivides(D int64, n *big.Int) bool {
	return new(big.Int).Rem(n, big.NewInt(D)).Sign() == 0
}

// TestHandDichotomy locks hit and trap witnesses computed by hand.
func TestHandDichotomy(t *testing.T) {
	if !IsTrapped(1, 2, 2, 1) || LeastRaw(1, 2, 2, 1) != -1 {
		t.Fatal("odd translation 1,3,5,... is trapped")
	}
	if IsFirstHit(1, 2, 2, 1, 0) || IsFirstHit(1, 2, 2, 1, 1) {
		t.Fatal("trapped translation was reported as a hit")
	}
	if !IsTrapped(-1, 0, 2, 1) {
		t.Fatal("the orbit 1,-1 is trapped")
	}
	if !IsFirstHit(2, 1, 3, 1, 1) || IsFirstHit(2, 1, 3, 1, 0) {
		t.Fatal("seed 1 with q=2,c=1,D=3 hits at time 1")
	}
	if IsFirstHit(2, 1, 3, 1, 2) || IsTrapped(2, 1, 3, 1) {
		t.Fatal("time 2 is after the hit, and the seed is not trapped")
	}
	if !IsFirstHit(1, 0, 2, 4, 0) || IsTrapped(1, 0, 2, 4) {
		t.Fatal("a divisible seed is a hit at time 0")
	}
	if !IsFirstHit(2, 1, -3, 1, 1) || IsTrapped(2, 1, -3, 1) {
		t.Fatal("negative divisor still hits at time 1")
	}
	if !IsTrapped(-2, 3, -5, -4) || LeastAffine(-2, 3, -5, -4) != -1 {
		t.Fatal("residues of -4 under q=-2,c=3,D=-5 avoid 0")
	}
	if RawAt(-2, 3, -5, -4, 4) != -79 || AffineState(-2, 3, 4, -4) != -79 {
		t.Fatal("hand prefix at time 4 is not -79")
	}
}

// TestPredicateRejectsConstantTrue fails when a classification predicate is
// replaced by a function that returns true on every input.
func TestPredicateRejectsConstantTrue(t *testing.T) {
	if IsFirstHit(1, 2, 2, 1, 0) {
		t.Fatal("first-hit predicate accepted a non-divisible time")
	}
	if IsFirstHit(2, 1, 3, 1, 2) {
		t.Fatal("first-hit predicate accepted a time after the hit")
	}
	if IsFirstHit(1, 0, 0, 1, 0) {
		t.Fatal("first-hit predicate accepted a zero divisor")
	}
	if IsTrapped(1, 0, 2, 4) {
		t.Fatal("trap predicate accepted an immediate division")
	}
	if IsTrapped(2, 1, 3, 1) {
		t.Fatal("trap predicate accepted a hit at time 1")
	}
	if IsTrapped(1, 1, 0, 1) {
		t.Fatal("trap predicate accepted a zero divisor")
	}
	if ExistsHitIffNotTrapped(1, 1, 0, 1) {
		t.Fatal("equivalence predicate accepted a zero divisor")
	}
	if ExistsHitIffNotTrapped(1, 1, 1, 1) {
		t.Fatal("equivalence predicate accepted a unit divisor")
	}
}

// TestGridMatchesClosedForm compares every int64 state with the closed form
// and requires the hit and trap sides to agree on the whole grid.
func TestGridMatchesClosedForm(t *testing.T) {
	var checks uint64
	for q := int64(-dichAbsQ); q <= dichAbsQ; q++ {
		for c := int64(-dichAbsC); c <= dichAbsC; c++ {
			for _, D := range dichDivisors {
				for n := int64(-dichAbsN); n <= dichAbsN; n++ {
					m := AbsInt(D)
					rawJ := -1
					affJ := -1
					for j := 0; j < int(m); j++ {
						gotAff := big.NewInt(AffineState(q, c, j, n))
						wantAff := BigAffine(q, c, j, n)
						if gotAff.Cmp(wantAff) != 0 {
							t.Fatalf("affine q=%d c=%d j=%d n=%d", q, c, j, n)
						}
						gotRaw := big.NewInt(RawAt(q, c, D, n, j))
						if gotRaw.Cmp(BigRaw(q, c, D, n, j)) != 0 {
							t.Fatalf("raw q=%d c=%d D=%d n=%d j=%d", q, c, D, n, j)
						}
						if rawJ < 0 && BigDivides(D, gotRaw) {
							rawJ = j
						}
						if affJ < 0 && BigDivides(D, gotAff) {
							affJ = j
						}
						checks++
					}
					if LeastRaw(q, c, D, n) != rawJ || LeastAffine(q, c, D, n) != affJ {
						t.Fatalf("least time q=%d c=%d D=%d n=%d", q, c, D, n)
					}
					if rawJ != affJ {
						t.Fatalf("sides differ q=%d c=%d D=%d n=%d", q, c, D, n)
					}
					if IsTrapped(q, c, D, n) != (rawJ < 0) {
						t.Fatalf("trap class q=%d c=%d D=%d n=%d", q, c, D, n)
					}
					if rawJ < 0 {
						if IsFirstHit(q, c, D, n, 0) {
							t.Fatalf("trap hit q=%d c=%d D=%d n=%d", q, c, D, n)
						}
					} else if !IsFirstHit(q, c, D, n, rawJ) {
						t.Fatalf("hit time q=%d c=%d D=%d n=%d j=%d", q, c, D, n, rawJ)
					}
					if !ExistsHitIffNotTrapped(q, c, D, n) {
						t.Fatalf("equivalence q=%d c=%d D=%d n=%d", q, c, D, n)
					}
					checks += dichPerSeed
				}
			}
		}
	}
	total := SweepDichotomy()
	if total.Failures != 0 {
		t.Fatalf("sweep failures: %d", total.Failures)
	}
	if total.Checks != ExpectedChecks() || total.Checks == 0 {
		t.Fatalf("check count: sweep %d, expected %d", total.Checks, ExpectedChecks())
	}
	if checks == 0 {
		t.Fatal("reference grid made no comparisons")
	}
}
