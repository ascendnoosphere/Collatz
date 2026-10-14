// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Exact binary-word checks and construction of a balanced cyclic cut.
package main

import (
	"fmt"
	"math/bits"
	"sync"
)

const MaxHalf uint = 10
const MaxLength uint = 2 * MaxHalf

// Word stores the first letter in bit zero; Length is always checked before use.
type Word struct {
	Bits   uint64
	Length uint
}

// Result records a complete census at one half-length, or an explicit failure.
type Result struct {
	Half     uint
	Checked  uint64
	Eligible uint64
	Err      error
}

// LowMask selects the lowest n machine bits, saturating at the machine width.
func LowMask(n uint) uint64 {
	if n >= 64 {
		return ^uint64(0)
	}
	return (uint64(1) << n) - 1
}

// ValidWord accepts precisely the supported even lengths and their bit masks.
func ValidWord(w Word) bool {
	return w.Length <= MaxLength && w.Length%2 == 0 && w.Bits&^LowMask(w.Length) == 0
}

// Rotate moves k initial letters to the end, including the empty-word case.
func Rotate(w Word, k uint) (Word, bool) {
	if !ValidWord(w) {
		return Word{}, false
	}
	if w.Length == 0 {
		return w, true
	}
	k %= w.Length
	return Word{
		Bits:   w.Bits>>k | (w.Bits&LowMask(k))<<(w.Length-k),
		Length: w.Length,
	}, true
}

// OddCount counts the ones in a supported word.
func OddCount(w Word) (uint, bool) {
	if !ValidWord(w) {
		return 0, false
	}
	return uint(bits.OnesCount64(w.Bits)), true
}

// Antipodal compares the two equal halves without rotating the word.
func Antipodal(w Word) (uint, bool) {
	if !ValidWord(w) {
		return 0, false
	}
	h := w.Length / 2
	return uint(bits.OnesCount64((w.Bits & LowMask(h)) ^ (w.Bits >> h))), true
}

// BalancedCut finds the first balanced cut in at most h sliding-window updates.
func BalancedCut(w Word) (uint, bool) {
	total, ok := OddCount(w)
	if !ok || total%2 != 0 {
		return 0, false
	}
	h := w.Length / 2
	target := total / 2
	count := uint(bits.OnesCount64(w.Bits & LowMask(h)))
	if count == target {
		return 0, true
	}
	// At cut k, the outgoing bit belongs to the counted window, so no underflow occurs.
	for k := uint(0); k < h; k++ {
		count -= uint(w.Bits >> k & 1)
		count += uint(w.Bits >> (k + h) & 1)
		if count == target {
			return k + 1, true
		}
	}
	return 0, false
}

// VerifyWord compares the direct classification with every cyclic cut and its witness.
func VerifyWord(w Word) error {
	if !ValidWord(w) {
		return fmt.Errorf("unsupported word length or mask")
	}
	h := w.Length / 2
	total, _ := OddCount(w)
	distance, _ := Antipodal(w)
	if total%2 != distance%2 {
		return fmt.Errorf("odd-count parity differs from distance parity")
	}
	left, right := w.Bits&LowMask(h), w.Bits>>h
	if (left == right) != (distance == 0) {
		return fmt.Errorf("repetition and zero distance disagree")
	}
	// A complete rotation census independently checks both directions of the transport test.
	period := w.Length
	if period == 0 {
		period = 1
	}
	transport := false
	for k := uint(0); k < period; k++ {
		r, _ := Rotate(w, k)
		count, _ := OddCount(r)
		d, _ := Antipodal(r)
		if count != total || d != distance {
			return fmt.Errorf("rotation %d changes a word invariant", k)
		}
		u, v := r.Bits&LowMask(h), r.Bits>>h
		if bits.OnesCount64(u) == bits.OnesCount64(v) && d == 2 {
			if bits.OnesCount64(u&^v) != 1 || bits.OnesCount64(v&^u) != 1 {
				return fmt.Errorf("transport does not move one letter in each direction")
			}
			transport = true
		}
	}
	if transport != (distance == 2) {
		return fmt.Errorf("transport and distance two disagree")
	}
	k, found := BalancedCut(w)
	if found != (total%2 == 0) {
		return fmt.Errorf("balanced-cut existence disagrees with even total")
	}
	if found {
		if k > h {
			return fmt.Errorf("balanced cut exceeds the half-turn budget")
		}
		r, _ := Rotate(w, k)
		if bits.OnesCount64(r.Bits&LowMask(h)) != bits.OnesCount64(r.Bits>>h) {
			return fmt.Errorf("constructed cut is not balanced")
		}
	}
	if total%2 == 0 && left != right && !transport && distance < 4 {
		return fmt.Errorf("gap hypotheses hold below distance four")
	}
	return nil
}

// ScanHalf enumerates every word of length 2h within the explicit finite budget.
func ScanHalf(h uint) Result {
	r := Result{Half: h}
	if h > MaxHalf {
		r.Err = fmt.Errorf("half-length exceeds %d", MaxHalf)
		return r
	}
	length := 2 * h
	limit := uint64(1) << length
	for mask := uint64(0); mask < limit; mask++ {
		w := Word{Bits: mask, Length: length}
		if err := VerifyWord(w); err != nil {
			r.Err = fmt.Errorf("half-length %d, mask %d: %w", h, mask, err)
			return r
		}
		r.Checked++
		count, _ := OddCount(w)
		distance, _ := Antipodal(w)
		if count%2 == 0 && distance >= 4 {
			r.Eligible++
		}
	}
	return r
}

// main runs independent half-length censuses and prints their results in order.
func main() {
	var rows [MaxHalf + 1]Result
	var workers sync.WaitGroup
	for h := uint(0); h <= MaxHalf; h++ {
		workers.Add(1)
		go func(h uint) {
			defer workers.Done()
			rows[h] = ScanHalf(h)
		}(h)
	}
	workers.Wait()
	fmt.Println("half-length words gap-eligible")
	for _, r := range rows {
		if r.Err != nil {
			panic(r.Err)
		}
		fmt.Printf("%d %d %d\n", r.Half, r.Checked, r.Eligible)
	}
}
