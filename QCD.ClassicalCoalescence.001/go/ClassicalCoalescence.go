// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

package main

import (
	"fmt"
	"math/big"
	"math/bits"
	"os"
)

// Workspace retains big-integer buffers for exact terminal-prefix trajectories.
type Workspace struct {
	Value    big.Int
	Power    big.Int
	Divisor  big.Int
	Quotient big.Int
	Expected big.Int
	Peak     big.Int
	One      big.Int
	Three    big.Int
}

// Prepare reserves the bounded terminal-test precision before stepping trajectories.
func (w *Workspace) Prepare() {
	w.One.SetInt64(1)
	w.Three.SetInt64(3)
	for _, z := range []*big.Int{
		&w.Value, &w.Power, &w.Divisor, &w.Quotient, &w.Expected, &w.Peak,
	} {
		z.Lsh(&w.One, 1024)
		z.SetInt64(0)
	}
}

// Apply takes one positive shortcut tick, reusing the prepared value buffer.
func (w *Workspace) Apply() {
	if w.Value.Bit(0) != 0 {
		w.Value.Mul(&w.Value, &w.Three)
		w.Value.Add(&w.Value, &w.One)
	}
	w.Value.Rsh(&w.Value, 1)
}

// Step evaluates bounded positive test states; the caller supplies overflow-safe ranges.
func Step(n uint64) uint64 {
	if n%2 == 0 {
		return n / 2
	}
	return (3*n + 1) / 2
}

// Power computes small exact integer powers used by the finite coefficient checks.
func Power(x uint64, n int) uint64 {
	y := uint64(1)
	for j := 0; j < n; j++ {
		y *= x
	}
	return y
}

// Residual tests the exact odd-burst data of the written residual set.
func Residual(n uint64) bool {
	if n == 0 || n%2 == 0 {
		return false
	}
	a := bits.TrailingZeros64(n + 1)
	u := (n + 1) >> a
	if a < 2 || u%3 == 0 {
		return false
	}
	return Power(3, a)*u%4 == 3
}

// VerifyFamilies compares the universal cylinder formulas with their actual branch words.
func VerifyFamilies(limit int) error {
	for t := 0; t <= limit; t++ {
		j := uint64(t)
		n, p := 4+9*j, 3+8*j
		x := p
		for k, parity := range [3]uint64{1, 1, 0} {
			if x%2 != parity {
				return fmt.Errorf("inverse 110 guard: t=%d tick=%d", t, k)
			}
			x = Step(x)
		}
		if x != n || p >= n || 9*p >= 8*n {
			return fmt.Errorf("inverse 110 identity: t=%d", t)
		}
		n, x = 11+32*j, 11+32*j
		for k, parity := range [5]uint64{1, 1, 0, 1, 0} {
			if x%2 != parity {
				return fmt.Errorf("11010 guard: t=%d tick=%d", t, k)
			}
			x = Step(x)
		}
		if x != 10+27*j || x >= n || (t >= 1 && 9*x > 8*n) {
			return fmt.Errorf("11010 endpoint: t=%d", t)
		}
		n, p = 10+81*j, 7+64*j
		x = p
		for k, parity := range [6]uint64{1, 1, 1, 0, 1, 0} {
			if x%2 != parity {
				return fmt.Errorf("inverse 111010 guard: t=%d tick=%d", t, k)
			}
			x = Step(x)
		}
		if x != n || p >= n || 9*p >= 8*n {
			return fmt.Errorf("inverse 111010 identity: t=%d", t)
		}
		n, p = 31+1152*j, 27+1024*j
		if !Residual(n) || Step(Step(Step(p))) != n || p >= n {
			return fmt.Errorf("residual cylinder: t=%d", t)
		}
	}
	return nil
}

// VerifyResidualRules checks recovery choices on a finite interval, not global completeness.
func VerifyResidualRules(limit uint64) error {
	for n := uint64(2); n <= limit; n++ {
		p := uint64(0)
		sourceTime, parentTime := 0, 0
		switch {
		case n%2 == 0:
			p, sourceTime = n/2, 1
		case n%4 == 1:
			p, sourceTime = (3*n+1)/4, 2
		case n%3 == 2:
			p, parentTime = (2*n-1)/3, 1
		default:
			a := bits.TrailingZeros64(n + 1)
			u := (n + 1) >> a
			if Power(3, a)*u%4 == 1 {
				p, sourceTime, parentTime = (n-1)/2, a+2, a+1
			} else if n%9 == 4 {
				p, parentTime = (8*n-5)/9, 3
			} else if n%32 == 11 {
				p, sourceTime = (27*n+23)/32, 5
			} else if n%81 == 10 {
				p, parentTime = (64*n-73)/81, 6
			}
		}
		if p == 0 {
			if !Residual(n) || n%9 == 4 || n%32 == 11 || n%81 == 10 {
				return fmt.Errorf("residual uncovered guard: n=%d", n)
			}
			continue
		}
		if p >= n || 9*p > 8*n {
			return fmt.Errorf("parent order: n=%d p=%d", n, p)
		}
		x, y := n, p
		for k := 0; k < sourceTime; k++ {
			x = Step(x)
		}
		for k := 0; k < parentTime; k++ {
			y = Step(y)
		}
		if x != y {
			return fmt.Errorf("parent join: n=%d p=%d", n, p)
		}
	}
	return nil
}

// WordData composes the shortcut rational branches in chronological bit order.
func WordData(mask uint64, h int) (int64, int64, int64) {
	p, q, b := int64(1), int64(1), int64(0)
	for j := 0; j < h; j++ {
		if mask>>j&1 != 0 {
			p, b = 3*p, 3*b+q
		}
		q *= 2
	}
	return p, q, b
}

// LegalRepeated tests complete copies without allocating a parity slice.
func LegalRepeated(mask uint64, h int, n uint64, k int) bool {
	for copy := 0; copy < k; copy++ {
		for j := 0; j < h; j++ {
			if n%2 != mask>>j&1 {
				return false
			}
			n = Step(n)
		}
	}
	return true
}

// VerifyBudgets checks all words through length eight against exact displacement divisibility.
func VerifyBudgets() (int, error) {
	count := 0
	for h := 1; h <= 8; h++ {
		for mask := uint64(0); mask < uint64(1)<<h; mask++ {
			p, q, b := WordData(mask, h)
			for n := uint64(1); n <= 256; n++ {
				d := (p-q)*int64(n) + b
				qk := int64(1)
				for k := 0; k <= 3; k++ {
					if LegalRepeated(mask, h, n, k) != (d%qk == 0) {
						return count, fmt.Errorf("budget: h=%d mask=%d n=%d k=%d", h, mask, n, k)
					}
					count++
					qk *= q
				}
			}
		}
	}
	return count, nil
}

// SupportNumerator computes ordered suffix weights on the bounded support window.
func SupportNumerator(mask uint64, h int) uint64 {
	a, multiplier := uint64(0), uint64(1)
	for j := h - 1; j >= 0; j-- {
		if mask>>j&1 != 0 {
			a += multiplier * (uint64(1) << j)
			multiplier *= 3
		}
	}
	return a
}

// VerifyCrossings exhausts windows through twelve with at most three interior common letters.
func VerifyCrossings() (int, error) {
	count := 0
	for h := 2; h <= 12; h++ {
		for lo := 0; lo < h; lo++ {
			for hi := lo + 1; hi < h; hi++ {
				endpoints := uint64(1)<<lo | uint64(1)<<hi
				interior := (uint64(1)<<hi - 1) & ^(uint64(1)<<(lo+1) - 1)
				for c := uint64(0); c < uint64(1)<<h; c++ {
					if c&endpoints != 0 || bits.OnesCount64(c&interior) > 3 {
						continue
					}
					r := bits.OnesCount64(c) + 1
					m := uint64(1)<<h + Power(3, r)
					u := SupportNumerator(c|uint64(1)<<lo, h)
					v := SupportNumerator(c|uint64(1)<<hi, h)
					if v <= u || (v-u)%m == 0 {
						return count, fmt.Errorf("crossing: h=%d lo=%d hi=%d c=%d", h, lo, hi, c)
					}
					count++
				}
			}
		}
	}
	return count, nil
}

// VerifyFiveCompositions checks the entire bounded exponent family, without orbit search.
func VerifyFiveCompositions() (int, error) {
	count := 0
	for a := 1; a <= 4; a++ {
		for b := 1; b <= 4; b++ {
			for c := 1; c <= 4; c++ {
				for d := 1; d <= 4; d++ {
					e := 8 - a - b - c - d
					if e < 1 {
						continue
					}
					n := 81 + 27*Power(2, a) + 9*Power(2, a+b) +
						3*Power(2, a+b+c) + Power(2, a+b+c+d)
					if n%13 == 0 {
						return count, fmt.Errorf("five composition: %d,%d,%d,%d,%d", a, b, c, d, e)
					}
					count++
				}
			}
		}
	}
	return count, nil
}

// VerifyTerminal checks endpoint, first-arrival and peak formulas with exact big integers.
func VerifyTerminal() error {
	var w Workspace
	w.Prepare()
	for a := 2; a <= 4; a++ {
		for t := 1; t <= 5; t += 2 {
			l := int(Power(3, a)) * t
			w.Power.Lsh(&w.One, uint(l))
			w.Quotient.Add(&w.Power, &w.One)
			w.Divisor.SetUint64(Power(3, a+1))
			w.Quotient.Quo(&w.Quotient, &w.Divisor)
			w.Value.Lsh(&w.Quotient, uint(a))
			w.Value.Sub(&w.Value, &w.One)
			w.Expected.Lsh(&w.One, uint(l-2))
			w.Peak.Sub(&w.Power, &w.One)
			w.Peak.Sub(&w.Peak, &w.One)
			w.Peak.Quo(&w.Peak, &w.Three)
			for j := 0; j <= a+l; j++ {
				if j < a+l && w.Value.Cmp(&w.One) <= 0 {
					return fmt.Errorf("terminal early hit: a=%d t=%d j=%d", a, t, j)
				}
				if j == a && w.Value.Cmp(&w.Peak) != 0 {
					return fmt.Errorf("terminal peak: a=%d t=%d", a, t)
				}
				if j != a && w.Value.Cmp(&w.Peak) >= 0 {
					return fmt.Errorf("terminal peak uniqueness: a=%d t=%d j=%d", a, t, j)
				}
				if j == a+2 && w.Value.Cmp(&w.Expected) != 0 {
					return fmt.Errorf("terminal endpoint: a=%d t=%d", a, t)
				}
				if j == a+l && w.Value.Cmp(&w.One) != 0 {
					return fmt.Errorf("terminal final hit: a=%d t=%d", a, t)
				}
				w.Apply()
			}
		}
	}
	return nil
}

// main executes the bounded consistency checks accompanying the written proofs.
func main() {
	if err := VerifyFamilies(10000); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := VerifyResidualRules(100000); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	budgets, err := VerifyBudgets()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	crossings, err := VerifyCrossings()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	compositions, err := VerifyFiveCompositions()
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err := VerifyTerminal(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	fmt.Printf("parent cylinders: t=0..10000; residual rules: n=2..100000\n")
	fmt.Printf("repeated-word instances: %d; crossing configurations: %d\n", budgets, crossings)
	fmt.Printf("five-return compositions: %d; terminal cases: 9\n", compositions)
}
