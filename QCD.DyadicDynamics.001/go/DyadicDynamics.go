// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"fmt"
	"math/big"
	"os"
)

// Workspace retains integer buffers across exact raw iterations.
type Workspace struct {
	next big.Int
}

// Apply performs division-first signed dynamics without allocating a new state per tick.
// The mutable state n must not alias the coefficient objects q and c.
func (w *Workspace) Apply(q, c, n *big.Int) {
	if n.Bit(0) == 0 {
		w.next.Rsh(n, 1)
	} else {
		w.next.Mul(q, n)
		w.next.Add(&w.next, c)
	}
	n.Set(&w.next)
}

// VerifyTail checks the initial clock and every shifted affine identity in a finite word.
func VerifyTail(q, c, seed int64, ticks int) error {
	if seed == 0 || (q+c)%2 == 0 || ticks < 0 {
		return fmt.Errorf("tail check requires a nonzero seed and opposite-parity coefficients")
	}
	var qb, cb, n, qm, initial, certificate, expected, power big.Int
	qb.SetInt64(q)
	cb.SetInt64(c)
	n.SetInt64(seed)
	qm.Sub(&qb, big.NewInt(1))
	var w Workspace
	for n.Bit(0) == 0 {
		w.Apply(&qb, &cb, &n)
	}
	initial.Mul(&qm, &n)
	initial.Add(&initial, &cb)
	power.SetInt64(1)
	for j := 0; j <= ticks; j++ {
		if n.Bit(0) == 0 {
			return fmt.Errorf("odd guard lost for (%d,%d), seed %d, tick %d", q, c, seed, j)
		}
		certificate.Mul(&qm, &n)
		certificate.Add(&certificate, &cb)
		expected.Mul(&power, &initial)
		if certificate.Cmp(&expected) != 0 {
			return fmt.Errorf("shift certificate failed for (%d,%d), seed %d", q, c, seed)
		}
		if j < ticks {
			w.Apply(&qb, &cb, &n)
			power.Mul(&power, &qb)
		}
	}
	return nil
}

// VerifyMersenne checks each power-of-two phase and rules out an earlier return to one.
func VerifyMersenne(k uint) error {
	var q, c, n, expected big.Int
	c.SetInt64(1)
	n.SetInt64(1)
	q.Lsh(&c, k)
	q.Sub(&q, &c)
	var w Workspace
	for j := uint(0); j <= k; j++ {
		w.Apply(&q, &c, &n)
		expected.Lsh(&c, k-j)
		if n.Cmp(&expected) != 0 {
			return fmt.Errorf("Mersenne phase mismatch for exponent %d at time %d", k, j+1)
		}
		if j < k && n.Cmp(&c) <= 0 {
			return fmt.Errorf("Mersenne period closed early for exponent %d", k)
		}
	}
	return nil
}

// VerifyUnit checks an actual raw capture time against the ceiling-logarithmic bound.
func VerifyUnit(seed int64) error {
	if seed <= 0 {
		return fmt.Errorf("unit capture requires a positive seed")
	}
	var q, c, n, boundPower big.Int
	q.SetInt64(1)
	c.SetInt64(1)
	n.SetInt64(seed)
	boundPower.SetInt64(1)
	h := 0
	for boundPower.Cmp(&n) < 0 {
		boundPower.Lsh(&boundPower, 1)
		h++
	}
	var w Workspace
	for j := 0; j <= 2*h; j++ {
		if n.Cmp(&c) == 0 {
			return nil
		}
		if j < 2*h {
			w.Apply(&q, &c, &n)
		}
	}
	return fmt.Errorf("unit capture exceeded 2 ceil(log2 n) for seed %d", seed)
}

// LegalWord checks the raw guard: an odd letter must be followed by an even letter.
func LegalWord(mask, h uint, circular bool) bool {
	for j := uint(1); j < h; j++ {
		if mask&(1<<j) != 0 && mask&(1<<(j-1)) != 0 {
			return false
		}
	}
	return !circular || h == 0 || mask&1 == 0 || mask&(1<<(h-1)) == 0
}

// WordCounts computes legal prefix and circular-word counts without orbit inference.
func WordCounts(h uint) (int, int) {
	words, periodic := 0, 0
	for mask := uint(0); mask < 1<<h; mask++ {
		if LegalWord(mask, h, false) {
			words++
		}
		if LegalWord(mask, h, true) {
			periodic++
		}
	}
	return words, periodic
}

// VerifyGoldenCylinders compares every parity cylinder against its exact Haar-size formula.
// The parameter guard bounds all raw integer intermediates inside int64 in this finite test.
func VerifyGoldenCylinders(q, c int64, h uint) error {
	if q%2 == 0 || c%2 == 0 || q < -7 || q > 7 || c < -7 || c > 7 || h > 12 {
		return fmt.Errorf("golden-cylinder check requires bounded odd coefficients and depth <=12")
	}
	count := make([]int, 1<<h)
	count = count[:len(count)]
	for seed := int64(0); seed < 1<<h; seed++ {
		n, mask := seed, uint(0)
		for j := uint(0); j < h; j++ {
			if n%2 == 0 {
				n /= 2
			} else {
				mask |= 1 << j
				n = q*n + c
			}
		}
		count[mask]++
	}
	for mask := uint(0); mask < 1<<h; mask++ {
		want := 0
		if LegalWord(mask, h, false) {
			a, delta := uint(0), uint(0)
			for j := uint(0); j < h; j++ {
				if mask&(1<<j) == 0 {
					a++
				}
			}
			if h > 0 && mask&(1<<(h-1)) != 0 {
				delta = 1
			}
			want = 1 << (h - a - delta)
		}
		if count[mask] != want {
			return fmt.Errorf("cylinder mismatch (%d,%d), depth %d, word %b: %d != %d",
				q, c, h, mask, count[mask], want)
		}
	}
	return nil
}

// BoundedBinomial evaluates word counts for 0 <= n <= 17; other arguments return zero.
func BoundedBinomial(n, k int64) int64 {
	if n < 0 || n > 17 || k < 0 || k > n {
		return 0
	}
	if k > n-k {
		k = n - k
	}
	value := int64(1)
	for j := int64(1); j <= k; j++ {
		value = value * (n - k + j) / j
	}
	return value
}

// VerifyGoldenStatistics checks word counts and both initial laws using integer numerators.
// At h <= 16, the cleared second-moment products are below 243 * 16^2 * 2^32 < 2^48.
func VerifyGoldenStatistics(h uint) error {
	if h == 0 || h > 16 {
		return fmt.Errorf("statistical word check requires depth between one and sixteen")
	}
	count := make([]int64, h+1)
	count = count[:len(count)]
	var haarTotal, haarMoment, total, moment, second int64
	for mask := uint(0); mask < 1<<h; mask++ {
		if !LegalWord(mask, h, false) {
			continue
		}
		b, delta := uint(0), uint(0)
		for j := uint(0); j < h; j++ {
			if mask&(1<<j) != 0 {
				b++
			}
		}
		if mask&(1<<(h-1)) != 0 {
			delta = 1
		}
		count[b]++
		// Clear the Haar denominator 2^h and the stationary denominator 3 * 2^h.
		haarWeight := int64(1) << (b - delta)
		firstFactor := int64(4)
		if mask&1 != 0 {
			firstFactor = 2
		}
		weight := firstFactor * haarWeight
		haarTotal += haarWeight
		haarMoment += haarWeight * int64(b)
		total += weight
		moment += weight * int64(b)
		second += weight * int64(b*b)
	}
	for b := uint(0); b <= h; b++ {
		want := BoundedBinomial(int64(h-b+1), int64(b))
		if count[b] != want {
			return fmt.Errorf("depth %d, %d ones: count %d != %d", h, b, count[b], want)
		}
	}
	scale, sign := int64(1)<<h, int64(1)
	if h%2 != 0 {
		sign = -1
	}
	if haarTotal != scale || total != 3*scale || moment != int64(h)*scale {
		return fmt.Errorf("normalization or stationary mean failed at depth %d", h)
	}
	if 9*haarMoment != (3*int64(h)+1)*scale-sign {
		return fmt.Errorf("Haar mean failed at depth %d", h)
	}
	// E[B_h^2] = h^2/9 + 2h/27 + 8(1 - (-1/2)^h)/81 has integral numerators.
	left := 81 * second * scale
	right := total * ((9*int64(h*h)+6*int64(h)+8)*scale - 8*sign)
	if left != right {
		return fmt.Errorf("stationary variance failed at depth %d", h)
	}
	return nil
}

// main validates finite moment identities before printing word and periodic-point counts.
func main() {
	for h := uint(1); h <= 16; h++ {
		if err := VerifyGoldenStatistics(h); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	}
	for h := uint(1); h <= 12; h++ {
		if err := VerifyGoldenCylinders(3, 1, h); err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		words, periodic := WordCounts(h)
		fmt.Printf("depth=%d raw_words=%d circular_words=%d\n", h, words, periodic)
	}
}
