// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"fmt"
	"math"
	"math/bits"
	"os"
	"sync"
)

// MaxHalfLength bounds both concatenations to 24 letters and all coefficients below 2^40.
const MaxHalfLength uint = 12

// MaxWordLength is the coefficient and parity-replay budget.
const MaxWordLength uint = 2 * MaxHalfLength

// Word records the first branch in its least significant bit; one denotes an odd branch.
type Word struct {
	Bits   uint64
	Length uint
}

// Workspace caches powers independently for each worker; pair checks allocate no buffers.
type Workspace struct {
	three [MaxWordLength + 1]uint64
}

// Result carries one half-length's complete finite enumeration.
type Result struct {
	HalfLength uint
	Checks     uint64
	Err        error
}

// ValidWord rejects unsupported lengths and bits outside the stated word.
func ValidWord(w Word) bool {
	return w.Length <= MaxWordLength && w.Bits>>w.Length == 0
}

// Append preserves the low-bit-first convention and the coefficient budget.
func Append(u, v Word) (Word, bool) {
	if !ValidWord(u) || !ValidWord(v) || u.Length+v.Length > MaxWordLength {
		return Word{}, false
	}
	return Word{Bits: u.Bits | v.Bits<<u.Length, Length: u.Length + v.Length}, true
}

// OddCount counts the affine branches of a supported word.
func OddCount(w Word) (uint, bool) {
	if !ValidWord(w) {
		return 0, false
	}
	return uint(bits.OnesCount64(w.Bits)), true
}

// Numerator evaluates the tail recurrence without division or floating-point arithmetic.
func Numerator(w Word) (uint64, bool) {
	if !ValidWord(w) {
		return 0, false
	}
	var value uint64
	power := uint64(1)
	for j := w.Length; j > 0; j-- {
		value *= 2
		if w.Bits>>(j-1)&1 != 0 {
			value += power
			power *= 3
		}
	}
	return value, true
}

// RunWord checks every parity before advancing and rejects an overflowing odd numerator.
func RunWord(w Word, n uint64) (uint64, bool) {
	if !ValidWord(w) {
		return 0, false
	}
	for j := uint(0); j < w.Length; j++ {
		if n&1 != w.Bits>>j&1 {
			return 0, false
		}
		if n&1 == 0 {
			n /= 2
		} else {
			if n > (math.MaxUint64-1)/3 {
				return 0, false
			}
			n = (3*n + 1) / 2
		}
	}
	return n, true
}

// GCD checks the arithmetic obstruction independently of the numerator identities.
func GCD(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// NewWorkspace initializes the exact powers used in the supported word range.
func NewWorkspace() Workspace {
	w := Workspace{}
	w.three[0] = 1
	for j := 1; j < len(w.three); j++ {
		w.three[j] = 3 * w.three[j-1]
	}
	return w
}

// VerifyPair checks the gap, both concatenations, coprimality and the return obstruction.
func (w *Workspace) VerifyPair(p, s Word) error {
	if !ValidWord(p) || !ValidWord(s) || p.Length+s.Length+2 > MaxHalfLength {
		return fmt.Errorf("unsupported prefix and suffix lengths")
	}
	if w.three[0] != 1 || w.three[MaxWordLength] != 282429536481 {
		return fmt.Errorf("workspace powers are not initialized")
	}
	// Insert 01 and 10 in chronological order; bit zero is the first letter.
	leftPrefix, _ := Append(p, Word{Bits: 2, Length: 2})
	rightPrefix, _ := Append(p, Word{Bits: 1, Length: 2})
	left, _ := Append(leftPrefix, s)
	right, _ := Append(rightPrefix, s)
	lr, _ := Append(left, right)
	rl, _ := Append(right, left)
	pOdd, _ := OddCount(p)
	sOdd, _ := OddCount(s)
	h, r := left.Length, pOdd+1+sOdd
	leftOdd, _ := OddCount(left)
	rightOdd, _ := OddCount(right)
	if h != right.Length || leftOdd != r || rightOdd != r {
		return fmt.Errorf("adjacent words have different shapes")
	}
	leftA, _ := Numerator(left)
	rightA, _ := Numerator(right)
	lrA, _ := Numerator(lr)
	rlA, _ := Numerator(rl)
	delta := (uint64(1) << p.Length) * w.three[sOdd]
	mu := (uint64(1) << p.Length) * w.three[r+sOdd]
	modulus := (uint64(1) << h) + w.three[r]
	if leftA != rightA+delta || lrA != modulus*rightA+mu ||
		rlA+mu != modulus*leftA {
		return fmt.Errorf("numerator transport identity failed")
	}
	if modulus < 7 || GCD(modulus, 2) != 1 || GCD(modulus, 3) != 1 ||
		GCD(modulus, mu) != 1 || mu%modulus == 0 {
		return fmt.Errorf("monomial obstruction failed")
	}
	if lrA%modulus != mu%modulus ||
		rlA%modulus != modulus-mu%modulus {
		return fmt.Errorf("concatenation residue failed")
	}
	// A positive return needs (2^(2h)-3^(2r))*n=A; a positive denominator contains M.
	two, three := uint64(1)<<(2*h), w.three[2*r]
	if two > three {
		denominator := two - three
		if denominator%modulus != 0 || lrA%denominator == 0 ||
			rlA%denominator == 0 {
			return fmt.Errorf("integer return obstruction failed")
		}
	} else if lrA == 0 || rlA == 0 {
		return fmt.Errorf("nonpositive return denominator has a zero numerator")
	}
	return nil
}

// ScanHalf checks every prefix/suffix split and every bit pattern at one supported length.
func ScanHalf(h uint) Result {
	out := Result{HalfLength: h}
	if h < 2 || h > MaxHalfLength {
		out.Err = fmt.Errorf("half-length must lie between 2 and %d", MaxHalfLength)
		return out
	}
	w := NewWorkspace()
	for pLength := uint(0); pLength <= h-2; pLength++ {
		sLength := h - 2 - pLength
		for pBits := uint64(0); pBits < uint64(1)<<pLength; pBits++ {
			for sBits := uint64(0); sBits < uint64(1)<<sLength; sBits++ {
				p, s := Word{pBits, pLength}, Word{sBits, sLength}
				if err := w.VerifyPair(p, s); err != nil {
					out.Err = fmt.Errorf("prefix %v, suffix %v: %w", p, s, err)
					return out
				}
				out.Checks++
			}
		}
	}
	return out
}

// main gives each independent half-length one worker and reports in increasing length.
func main() {
	results := make([]Result, MaxHalfLength-1)
	var workers sync.WaitGroup
	for j := range results {
		workers.Add(1)
		go func(j int) {
			defer workers.Done()
			results[j] = ScanHalf(uint(j) + 2)
		}(j)
	}
	workers.Wait()
	var total uint64
	for _, row := range results {
		if row.Err != nil {
			fmt.Fprintln(os.Stderr, row.Err)
			os.Exit(1)
		}
		fmt.Printf("half-length %d: %d adjacent pairs checked\n", row.HalfLength, row.Checks)
		total += row.Checks
	}
	fmt.Printf("%d pairs checked; both return obstructions hold in this range\n", total)
}
