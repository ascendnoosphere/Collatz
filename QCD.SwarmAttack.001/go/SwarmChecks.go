// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Package main checks word budgets, uniform cylinders, and cycles of ranks six to nine.
package main

import (
	"fmt"
	"math/big"
	"os"
)

// CheckRepeatedWords compares branch-by-branch legality with the signed-defect criterion.
// Length is at most seven, there are at most four copies, and seeds are below 128.
// Every intermediate state plus one is at most 128 * 2^28, so int64 is sufficient.
func CheckRepeatedWords() (int, error) {
	checks := 0
	for length := 0; length <= 7; length++ {
		for word := 0; word < 1<<length; word++ {
			p, q, b := int64(1), int64(1), int64(0)
			for tick := 0; tick < length; tick++ {
				if word>>tick&1 != 0 {
					p, b = 3*p, 3*b+q
				}
				q *= 2
			}
			for seed := int64(0); seed < 128; seed++ {
				defect, denominator := (p-q)*seed+b, int64(1)
				for copies := 0; copies <= 4; copies++ {
					state, legal := seed, true
					for tick := 0; tick < copies*length; tick++ {
						odd := int64(word >> (tick % length) & 1)
						if state%2 != odd {
							legal = false
							break
						}
						if odd == 1 {
							state = (3*state + 1) / 2
						} else {
							state /= 2
						}
					}
					if legal != (defect%denominator == 0) {
						return checks, fmt.Errorf("word=%d length=%d seed=%d copies=%d",
							word, length, seed, copies)
					}
					checks++
					denominator *= q
				}
			}
		}
	}
	return checks, nil
}

// CheckCylinder proves T^h(source+modulus*t)=target+slope*t for every t >= 0.
// Coefficients are uint64 inputs; intermediate arithmetic has arbitrary precision.
// A nonempty binary word supplies every parity guard, without sampling parameters.
func CheckCylinder(source, modulus, target, slope uint64, word string) error {
	if source == 0 || modulus == 0 || target == 0 || word == "" {
		return fmt.Errorf("cylinder requires positive source, modulus, target and a word")
	}
	var x, y big.Int
	// Reserve two extra bits per tick, enough even before dividing an odd branch.
	x.SetBit(&x, 64+2*len(word), 1)
	y.SetBit(&y, 64+2*len(word), 1)
	x.SetUint64(source)
	y.SetUint64(modulus)
	one, three := big.NewInt(1), big.NewInt(3)
	for tick := 0; tick < len(word); tick++ {
		bit := word[tick]
		if bit != '0' && bit != '1' {
			return fmt.Errorf("nonbinary letter at tick %d", tick)
		}
		// An even slope fixes the branch for the whole nonnegative parameter ray.
		if y.Bit(0) != 0 || x.Bit(0) != uint(bit-'0') {
			return fmt.Errorf("nonuniform parity guard at tick %d", tick)
		}
		if bit == '1' {
			x.Mul(&x, three)
			x.Add(&x, one)
			y.Mul(&y, three)
		}
		x.Rsh(&x, 1)
		y.Rsh(&y, 1)
	}
	if !x.IsUint64() || x.Uint64() != target ||
		!y.IsUint64() || y.Uint64() != slope {
		return fmt.Errorf("endpoint coefficients disagree")
	}
	return nil
}

// CheckDirectCylinder also proves positivity and strict descent on the entire ray.
func CheckDirectCylinder(source, modulus, target, slope uint64, word string) error {
	if err := CheckCylinder(source, modulus, target, slope, word); err != nil {
		return err
	}
	if target >= source || slope > modulus {
		return fmt.Errorf("identity is not a uniform strict descent")
	}
	return nil
}

// CountCycleWords tests every positive composition of total into rank exponents.
// The accepted range bounds each numerator by 9 * 3^8 * 2^18 < 2^34.
// Prefix sums and powers are preallocated; the recursive traversal allocates no buffers.
func CountCycleWords(rank, total int) (words, hits int, err error) {
	if rank < 6 || rank > 9 || total < rank || total > 2*rank {
		return 0, 0, fmt.Errorf("unsupported cycle range: rank=%d total=%d", rank, total)
	}
	var powers [10]uint64
	powers[0] = 1
	for i := 1; i <= rank; i++ {
		powers[i] = 3 * powers[i-1]
	}
	power := uint64(1) << total
	if power <= powers[rank] {
		return 0, 0, fmt.Errorf("nonpositive cycle denominator")
	}
	denominator := power - powers[rank]
	var prefix [9]uint
	var visit func(int, int, int)
	// Only the last exponent is forced; all earlier positive choices are enumerated.
	visit = func(index, remaining, sum int) {
		prefix[index] = uint(sum)
		if index == rank-1 {
			var numerator uint64
			for j := 0; j < rank; j++ {
				numerator += powers[rank-1-j] << prefix[j]
			}
			words++
			if numerator%denominator == 0 {
				hits++
			}
			return
		}
		for exponent := 1; exponent <= remaining-(rank-index-1); exponent++ {
			visit(index+1, remaining-exponent, sum+exponent)
		}
	}
	visit(0, total, 0)
	return words, hits, nil
}

// CheckCycleWindow exhausts 3^rank < 2^total <= (10/3)^rank for ranks six to nine.
// Any non-unit positive cycle has all states at least three, so its exponent total
// lies in this window. The wider bound total <= 2*rank follows from 3 + 1/x <= 4.
func CheckCycleWindow() error {
	for rank := 6; rank <= 9; rank++ {
		three, ten := uint64(1), uint64(1)
		for i := 0; i < rank; i++ {
			three, ten = 3*three, 10*ten
		}
		for total := rank; total <= 2*rank; total++ {
			power := uint64(1) << total
			if power <= three || power*three > ten {
				continue
			}
			words, hits, err := CountCycleWords(rank, total)
			if err != nil {
				return err
			}
			fmt.Printf("rank=%d total=%d compositions=%d divisible=%d\n",
				rank, total, words, hits)
			if hits != 0 {
				return fmt.Errorf("cycle candidate found at rank %d", rank)
			}
		}
	}
	return nil
}

// main runs the finite checks; neither check establishes capture or arbitrary-rank exclusion.
func main() {
	checks, err := CheckRepeatedWords()
	if err == nil {
		fmt.Printf("repeated-word checks=%d\n", checks)
		err = CheckCycleWindow()
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
