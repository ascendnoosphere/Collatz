// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"math"
	"testing"
)

// TestPairEnumeration checks every supported half-length and the exact enumeration count.
func TestPairEnumeration(t *testing.T) {
	var total uint64
	for h := uint(2); h <= MaxHalfLength; h++ {
		row := ScanHalf(h)
		want := uint64(h-1) << (h - 2)
		if row.Err != nil || row.Checks != want {
			t.Fatalf("half-length %d: got %+v, want %d checks", h, row, want)
		}
		total += row.Checks
	}
	if total != 20481 {
		t.Fatalf("got %d pairs, want 20481", total)
	}
}

// TestEmptyPair fixes the bit convention and the smallest nonzero residues.
func TestEmptyPair(t *testing.T) {
	left, right := Word{Bits: 2, Length: 2}, Word{Bits: 1, Length: 2}
	lr, ok := Append(left, right)
	if !ok || lr.Bits != 6 || lr.Length != 4 {
		t.Fatal("0110 was not concatenated in chronological order")
	}
	rl, ok := Append(right, left)
	if !ok || rl.Bits != 9 || rl.Length != 4 {
		t.Fatal("1001 was not concatenated in chronological order")
	}
	lrA, _ := Numerator(lr)
	rlA, _ := Numerator(rl)
	if lrA != 10 || rlA != 11 || lrA%7 != 3 || rlA%7 != 4 {
		t.Fatal("empty-surrounding residues differ")
	}
	w := NewWorkspace()
	if err := w.VerifyPair(Word{}, Word{}); err != nil {
		t.Fatal(err)
	}
}

// TestNonemptyPair checks the displayed example with nonempty surroundings.
func TestNonemptyPair(t *testing.T) {
	p, s := Word{Bits: 1, Length: 1}, Word{Length: 1}
	leftPrefix, _ := Append(p, Word{Bits: 2, Length: 2})
	rightPrefix, _ := Append(p, Word{Bits: 1, Length: 2})
	left, _ := Append(leftPrefix, s)
	right, _ := Append(rightPrefix, s)
	lr, _ := Append(left, right)
	rl, _ := Append(right, left)
	leftA, _ := Numerator(left)
	rightA, _ := Numerator(right)
	lrA, _ := Numerator(lr)
	rlA, _ := Numerator(rl)
	if leftA != 7 || rightA != 5 || lrA != 143 || rlA != 157 ||
		lrA%25 != 18 || rlA%25 != 7 {
		t.Fatal("nonempty-surrounding numerators differ")
	}
	w := NewWorkspace()
	if err := w.VerifyPair(p, s); err != nil {
		t.Fatal(err)
	}
}

// TestAffineIdentity replays actual parity words for 1024 seeds at every length through 10.
func TestAffineIdentity(t *testing.T) {
	w := NewWorkspace()
	for seed := uint64(0); seed < 1024; seed++ {
		state, word := seed, Word{}
		for h := uint(0); h <= 10; h++ {
			run, ok := RunWord(word, seed)
			count, _ := OddCount(word)
			numerator, _ := Numerator(word)
			if !ok || run != state || (uint64(1)<<h)*run != w.three[count]*seed+numerator {
				t.Fatalf("affine identity failed at seed %d, length %d", seed, h)
			}
			if h < 10 {
				word.Bits |= (state & 1) << h
				word.Length++
				if state&1 == 0 {
					state /= 2
				} else {
					state = (3*state + 1) / 2
				}
			}
		}
	}
}

// TestOrdinaryCycle distinguishes a repeated half from the excluded adjacent-swap pair.
func TestOrdinaryCycle(t *testing.T) {
	for _, row := range []struct {
		word Word
		seed uint64
	}{
		{Word{Bits: 1, Length: 2}, 1},
		{Word{Bits: 2, Length: 2}, 2},
		{Word{Bits: 5, Length: 4}, 1},
		{Word{Bits: 10, Length: 4}, 2},
	} {
		run, ok := RunWord(row.word, row.seed)
		if !ok || run != row.seed {
			t.Fatalf("ordinary cycle failed at %+v", row)
		}
	}
}

// TestWordBoundaries rejects extra bits, unsupported lengths and overflowing replay.
func TestWordBoundaries(t *testing.T) {
	for _, word := range []Word{
		{Bits: 1, Length: 0},
		{Bits: 4, Length: 2},
		{Length: MaxWordLength + 1},
		{Length: ^uint(0)},
	} {
		if ValidWord(word) {
			t.Fatalf("accepted malformed word %+v", word)
		}
		if _, ok := Numerator(word); ok {
			t.Fatal("numerator accepted malformed word")
		}
		if _, ok := OddCount(word); ok {
			t.Fatal("odd count accepted malformed word")
		}
		if _, ok := RunWord(word, 1); ok {
			t.Fatal("replay accepted malformed word")
		}
		if _, ok := Append(word, Word{}); ok {
			t.Fatal("append accepted malformed word")
		}
	}
	long := Word{Bits: (uint64(1) << MaxWordLength) - 1, Length: MaxWordLength}
	numerator, ok := Numerator(long)
	if !ok || numerator != 282412759265 {
		t.Fatal("maximum-length numerator differs")
	}
	if _, ok := Append(long, Word{Length: 1}); ok {
		t.Fatal("append exceeded its coefficient budget")
	}
	if run, ok := RunWord(Word{}, math.MaxUint64); !ok || run != math.MaxUint64 {
		t.Fatal("empty word is not the identity")
	}
	if _, ok := RunWord(Word{Bits: 1, Length: 1}, math.MaxUint64); ok {
		t.Fatal("overflowing odd numerator was accepted")
	}
	if _, ok := RunWord(Word{Bits: 1, Length: 1}, 2); ok {
		t.Fatal("wrong first parity was accepted")
	}
}

// TestPairBoundaries checks the full length budget and the required workspace constructor.
func TestPairBoundaries(t *testing.T) {
	w := NewWorkspace()
	p := Word{Bits: 1023, Length: 10}
	if err := w.VerifyPair(p, Word{}); err != nil {
		t.Fatal(err)
	}
	if err := w.VerifyPair(Word{Length: 11}, Word{}); err == nil {
		t.Fatal("half-length budget was ignored")
	}
	if err := w.VerifyPair(Word{Length: ^uint(0)}, Word{}); err == nil {
		t.Fatal("unsupported length wrapped its budget")
	}
	var zero Workspace
	if err := zero.VerifyPair(Word{}, Word{}); err == nil {
		t.Fatal("uninitialized workspace was accepted")
	}
	for _, h := range []uint{0, 1, MaxHalfLength + 1, ^uint(0)} {
		if row := ScanHalf(h); row.Err == nil || row.Checks != 0 {
			t.Fatalf("unsupported half-length %d was scanned", h)
		}
	}
}

// TestPairAllocations ensures successful hot-loop checks reuse the worker's cache.
func TestPairAllocations(t *testing.T) {
	w := NewWorkspace()
	p, s := Word{Bits: 5, Length: 3}, Word{Bits: 19, Length: 5}
	allocations := testing.AllocsPerRun(1000, func() {
		if err := w.VerifyPair(p, s); err != nil {
			panic(err)
		}
	})
	if allocations != 0 {
		t.Fatalf("pair check allocated %g objects", allocations)
	}
}
