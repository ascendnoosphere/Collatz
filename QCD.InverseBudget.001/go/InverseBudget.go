// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// InverseBudget checks denominator budgets and bounded ascending inverse trees.
package main

import "fmt"

const (
	LetterAffine   = byte(0)
	LetterDivision = byte(1)
	WordCap        = 16
	NodeCap        = 64
)

// MulOK returns a*b when the product fits in uint64.
func MulOK(a, b uint64) (uint64, bool) {
	if a == 0 || b == 0 {
		return 0, true
	}
	prod := a * b
	if prod/a != b {
		return 0, false
	}
	return prod, true
}

// AddOK returns a+b when the sum fits in uint64.
func AddOK(a, b uint64) (uint64, bool) {
	sum := a + b
	if sum < a {
		return 0, false
	}
	return sum, true
}

// PowIter returns base^exp by successive multiplication.
func PowIter(base, exp uint64) (uint64, bool) {
	if exp == 0 || base == 1 {
		return 1, true
	}
	if base == 0 {
		return 0, true
	}
	if exp >= 64 {
		return 0, false
	}
	acc := uint64(1)
	var i uint64
	for i = 0; i < exp; i++ {
		next, ok := MulOK(acc, base)
		if !ok {
			return 0, false
		}
		acc = next
	}
	return acc, true
}

// PowSquare returns base^exp by squaring, for comparison with PowIter.
func PowSquare(base, exp uint64) (uint64, bool) {
	acc := uint64(1)
	b := base
	e := exp
	for e > 0 {
		if e%2 == 1 {
			next, ok := MulOK(acc, b)
			if !ok {
				return 0, false
			}
			acc = next
		}
		e /= 2
		if e > 0 {
			next, ok := MulOK(b, b)
			if !ok {
				return 0, false
			}
			b = next
		}
	}
	return acc, true
}

// BelowBudget reports whether D^e < R^s, with overflow treated as unknown.
func BelowBudget(D, R, e, s uint64) (holds bool, known bool) {
	if D < 2 || R < 2 {
		return false, false
	}
	left, lok := PowIter(D, e)
	right, rok := PowIter(R, s)
	if !lok || !rok {
		return false, false
	}
	return left < right, true
}

// Replay reads word[:n] from p and reports legality of every letter.
func Replay(word *[WordCap]byte, n int, p, q, c, D uint64) (uint64, bool) {
	if word == nil || D < 2 || q < 1 || c < 1 || n < 0 || n > WordCap {
		return 0, false
	}
	i := 0
	for i < n {
		if word[i] == LetterAffine {
			if p%D == 0 {
				return 0, false
			}
			prod, ok := MulOK(q, p)
			if !ok {
				return 0, false
			}
			sum, ok := AddOK(prod, c)
			if !ok {
				return 0, false
			}
			p = sum
		} else if word[i] == LetterDivision {
			if p%D != 0 {
				return 0, false
			}
			p /= D
		} else {
			return 0, false
		}
		i++
	}
	return p, true
}

// OffsetOf evaluates the head-first offset by scanning from the tail.
func OffsetOf(word *[WordCap]byte, n int, q, D uint64) (uint64, bool) {
	if word == nil || n < 0 || n > WordCap {
		return 0, false
	}
	off := uint64(0)
	aff := uint64(0)
	i := n
	for i > 0 {
		i--
		if word[i] == LetterAffine {
			pwr, ok := PowIter(q, aff)
			if !ok {
				return 0, false
			}
			sum, ok := AddOK(off, pwr)
			if !ok {
				return 0, false
			}
			off = sum
			aff++
		} else if word[i] == LetterDivision {
			prod, ok := MulOK(off, D)
			if !ok {
				return 0, false
			}
			off = prod
		} else {
			return 0, false
		}
	}
	return off, true
}

// Solve returns a positive legal start for a word containing an affine letter.
func Solve(word *[WordCap]byte, n int, m, q, c, D uint64) (uint64, bool) {
	if word == nil || n <= 0 || n > WordCap || q == 0 || c == 0 || D < 2 {
		return 0, false
	}
	aff := uint64(0)
	div := uint64(0)
	i := 0
	for i < n {
		if word[i] == LetterAffine {
			aff++
		} else if word[i] == LetterDivision {
			div++
		} else {
			return 0, false
		}
		i++
	}
	if aff == 0 {
		return 0, false
	}
	off, ok := OffsetOf(word, n, q, D)
	if !ok {
		return 0, false
	}
	dpow, ok := PowIter(D, div)
	if !ok {
		return 0, false
	}
	rhs, ok := MulOK(dpow, m)
	if !ok {
		return 0, false
	}
	coff, ok := MulOK(c, off)
	if !ok || rhs < coff {
		return 0, false
	}
	numer := rhs - coff
	qpow, ok := PowIter(q, aff)
	if !ok || qpow == 0 || numer%qpow != 0 {
		return 0, false
	}
	p := numer / qpow
	if p < 1 {
		return 0, false
	}
	end, legal := Replay(word, n, p, q, c, D)
	if !legal || end != m {
		return 0, false
	}
	return p, true
}

// Workspace is one inverse walk from a fixed terminal value.
type Workspace struct {
	m, q, c, D, R uint64
	maxS          int
	nodes         [NodeCap]uint64
	nNodes        int
	nPaths        int
	overflow      bool
	truncated     bool
}

// Note stores a start once and counts every ascending path.
func (s *Workspace) Note(p uint64) {
	s.nPaths++
	i := 0
	for i < s.nNodes {
		if s.nodes[i] == p {
			return
		}
		i++
	}
	if s.nNodes == NodeCap {
		s.truncated = true
		return
	}
	s.nodes[s.nNodes] = p
	s.nNodes++
}

// DivPossible reports whether another division can still meet the ceiling.
func (s *Workspace) DivPossible(div int) bool {
	if s.maxS <= 0 || div < 0 {
		return false
	}
	holds, known := BelowBudget(s.D, s.R, uint64(div), uint64(s.maxS))
	if !known {
		s.overflow = true
		return false
	}
	return holds
}

// WalkBack extends the inverse tree by one affine or division predecessor.
func (s *Workspace) WalkBack(y uint64, aff, div int) {
	if s.overflow || s.truncated {
		return
	}
	if aff > 0 && y >= 1 && y < s.m {
		holds, known := BelowBudget(s.D, s.R, uint64(div), uint64(aff))
		if !known {
			s.overflow = true
			return
		}
		if holds {
			s.Note(y)
		}
	}
	if aff < s.maxS && y >= s.c && s.q != 0 && (y-s.c)%s.q == 0 {
		p := (y - s.c) / s.q
		if p >= 1 && s.D != 0 && p%s.D != 0 {
			s.WalkBack(p, aff+1, div)
		}
	}
	if s.DivPossible(div + 1) {
		prod, ok := MulOK(s.D, y)
		if !ok {
			s.overflow = true
			return
		}
		s.WalkBack(prod, aff, div+1)
	}
}

// CountInverse counts ascending starts with at most maxS affine letters.
func CountInverse(m, q, c, D uint64, maxS int) (int, int, bool) {
	if D < 2 || q < 1 || c < 1 || m < 1 || maxS < 1 || maxS > WordCap {
		return 0, 0, false
	}
	R, ok := AddOK(q, c)
	if !ok {
		return 0, 0, false
	}
	if _, ok := PowIter(R, uint64(maxS)); !ok {
		return 0, 0, false
	}
	var s Workspace
	s.m = m
	s.q = q
	s.c = c
	s.D = D
	s.R = R
	s.maxS = maxS
	s.WalkBack(m, 0, 0)
	if s.overflow || s.truncated {
		return 0, 0, false
	}
	return s.nNodes, s.nPaths, true
}

// WalkForward tests an ascending hit; a representable budget bounds divisions by 63.
func WalkForward(seed, m, q, c, D uint64, maxS int) (bool, int, int, bool) {
	if D < 2 || q < 1 || c < 1 || seed < 1 || maxS < 1 || maxS > WordCap {
		return false, 0, 0, false
	}
	R, ok := AddOK(q, c)
	if !ok {
		return false, 0, 0, false
	}
	if _, ok := PowIter(R, uint64(maxS)); !ok {
		return false, 0, 0, false
	}
	if seed >= m {
		return false, 0, 0, true
	}
	p := seed
	aff := 0
	div := 0
	steps := 0
	limit := maxS + 64
	for p != m && steps < limit {
		steps++
		if p%D == 0 {
			p /= D
			div++
			if p == 0 {
				return false, aff, div, true
			}
			continue
		}
		if aff >= maxS {
			return false, aff, div, true
		}
		prod, ok := MulOK(q, p)
		if !ok {
			return false, aff, div, false
		}
		sum, ok := AddOK(prod, c)
		if !ok {
			return false, aff, div, false
		}
		p = sum
		aff++
	}
	if p != m {
		return false, aff, div, true
	}
	if seed < m && aff >= 1 {
		return true, aff, div, true
	}
	return false, aff, div, true
}

// CountForward counts seeds below m whose raw orbit hits m within maxS.
func CountForward(m, q, c, D uint64, maxS int) (int, bool) {
	if D < 2 || q < 1 || c < 1 || m < 1 || maxS < 1 || maxS > WordCap {
		return 0, false
	}
	R, ok := AddOK(q, c)
	if !ok {
		return 0, false
	}
	if _, ok := PowIter(R, uint64(maxS)); !ok {
		return 0, false
	}
	n := 0
	var seed uint64 = 1
	for seed < m {
		hit, aff, div, ok := WalkForward(seed, m, q, c, D, maxS)
		if !ok {
			return 0, false
		}
		if hit {
			holds, known := BelowBudget(D, R, uint64(div), uint64(aff))
			if !known {
				return 0, false
			}
			if !holds {
				return n, false
			}
			n++
		}
		seed++
	}
	return n, true
}

// ImplicationFailures checks representable powers in a bounded budget grid.
func ImplicationFailures(maxBase, maxExp uint64) (int, bool) {
	if maxBase < 2 || maxBase > 32 || maxExp < 1 || maxExp > 64 {
		return 0, false
	}
	fails := 0
	var D uint64
	for D = 2; D <= maxBase; D++ {
		var R uint64 = 2
		for R <= maxBase {
			var e uint64
			for e = 0; e <= maxExp; e++ {
				var s uint64 = 1
				for s <= maxExp {
					left, lok := PowIter(D, e)
					right, rok := PowIter(R, s)
					alt, aok := PowSquare(R, s)
					if lok && rok && aok && alt != right {
						return fails, false
					}
					baseAlt, bok := PowSquare(D, e)
					if lok && bok && baseAlt != left {
						return fails, false
					}
					if lok && rok && left < right && !(e < right) {
						fails++
					}
					s++
				}
			}
			R++
		}
	}
	return fails, true
}

// MonotoneFailures checks power monotonicity; -1 denotes an unsupported grid.
func MonotoneFailures(maxBase, maxExp uint64) int {
	if maxBase < 2 || maxBase > 32 || maxExp < 1 || maxExp > 64 {
		return -1
	}
	fails := 0
	var base uint64 = 2
	for base <= maxBase {
		prev := uint64(1)
		var exp uint64 = 1
		for exp <= maxExp {
			next, ok := PowIter(base, exp)
			if !ok {
				break
			}
			if next < prev {
				fails++
			}
			prev = next
			exp++
		}
		base++
	}
	return fails
}

// NecessityFailures counts ascending hits that violate the budget.
func NecessityFailures(maxD, maxQ, maxC, maxM uint64, maxS int) (int, bool) {
	if maxD < 2 || maxD > 8 || maxQ < 1 || maxQ > 8 || maxC < 1 || maxC > 8 ||
		maxM < 2 || maxM > 64 || maxS < 1 || maxS > WordCap {
		return 0, false
	}
	fails := 0
	var D uint64 = 2
	for D <= maxD {
		var q uint64 = 1
		for q <= maxQ {
			var c uint64 = 1
			for c <= maxC {
				var m uint64 = 2
				for m <= maxM {
					var seed uint64 = 1
					for seed < m {
						hit, aff, div, ok := WalkForward(seed, m, q, c, D, maxS)
						if !ok {
							return fails, false
						}
						if hit {
							holds, known := BelowBudget(D, q+c, uint64(div), uint64(aff))
							if !known || !holds {
								fails++
							}
						}
						seed++
					}
					m++
				}
				c++
			}
			q++
		}
		D++
	}
	return fails, true
}

// VerifyWordCounts compares binary-word enumeration with Pascal's recurrence.
func VerifyWordCounts(maxLength int) error {
	if maxLength < 0 || maxLength > WordCap {
		return fmt.Errorf("word length must be between 0 and %d", WordCap)
	}
	var expected, counts [WordCap + 1]int
	expected[0] = 1
	for h := 0; h <= maxLength; h++ {
		clear(counts[:])
		for mask := 0; mask < 1<<h; mask++ {
			s := 0
			for j := 0; j < h; j++ {
				if byte((mask>>j)&1) == LetterAffine {
					s++
				}
			}
			counts[s]++
		}
		for s := 0; s <= h; s++ {
			if counts[s] != expected[s] {
				return fmt.Errorf("length %d, affine count %d: got %d, want %d",
					h, s, counts[s], expected[s])
			}
		}
		if h < maxLength {
			for s := h + 1; s > 0; s-- {
				expected[s] += expected[s-1]
			}
		}
	}
	return nil
}

// main checks word enumeration, one inverse tree, and a bounded budget grid.
func main() {
	if err := VerifyWordCounts(WordCap); err != nil {
		panic(err)
	}
	nodes, paths, ok := CountInverse(8, 3, 1, 2, 3)
	fwd, fok := CountForward(8, 3, 1, 2, 3)
	impl, iok := ImplicationFailures(8, 12)
	mono := MonotoneFailures(8, 12)
	need, nok := NecessityFailures(4, 4, 4, 12, 3)
	fmt.Printf("inverse nodes=%d paths=%d ok=%t\n", nodes, paths, ok)
	fmt.Printf("forward nodes=%d ok=%t\n", fwd, fok)
	fmt.Printf("implication failures=%d ok=%t\n", impl, iok)
	fmt.Printf("monotone failures=%d\n", mono)
	fmt.Printf("necessity failures=%d ok=%t\n", need, nok)
	if !ok || !fok || !iok || !nok || nodes != fwd || impl != 0 || mono != 0 || need != 0 {
		panic("inverse-budget check failed")
	}
	fmt.Printf("word counts verified through length %d\n", WordCap)
}
