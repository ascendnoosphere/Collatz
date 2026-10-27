// SPDX-License-Identifier: CC-BY-4.0
// Copyright (c) 2026 ascendnoosphere

// Command SignedReturnResidue checks the affine cast on one finite grid.
// The residue of q^j*n + c*U_j(q) modulo |D| is the j-th iterate of
// r |-> q*r+c, for every |D| from 2 through 12 and every time through 12.
// The same grid checks the first-hit criterion and its invariance under
// addition of D. All arithmetic is exact int64 on the stated bounds.
// Agreement on this grid is not a proof for every integer parameter.
package main

import (
	"fmt"
	"os"
	"sync"
)

// Bounds of the exact grid. Multipliers and offsets run through
// [-castQAbs, castQAbs], seeds through [-castNAbs, castNAbs], times through
// 0..castJMax, and divisors through both signs of castDMin..castDMax.
// The shifted seed n+D then satisfies |n+D| <= 20. With |q| <= 4 and j <= 12,
// |q|^j <= 4^12 = 16777216, so
// |q|^j*|n+D| + |c|*U <= 16777216*20 + 4*(4^12-1)/3 = 357913940.
// The unused next power 4^13 = 67108864 also fits. Every product used below
// fits in an int64.
const (
	castQAbs    = 4
	castCAbs    = 4
	castNAbs    = 8
	castDMin    = 2
	castDMax    = 12
	castJMax    = 12
	castWorkers = 4
)

// Totals counts comparisons and disagreements of one sweep.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// Check records one comparison.
func (t *Totals) Check(ok bool) {
	t.Checks++
	if !ok {
		t.Failures++
	}
}

// Add accumulates a worker total into the receiver.
func (t *Totals) Add(other Totals) {
	t.Checks += other.Checks
	t.Failures += other.Failures
}

// Cache holds q^j and the offset sum U_j(q) through time castJMax.
// Load refills the existing buffers. A cache is not safe for concurrent calls.
type Cache struct {
	Pow  []int64
	Trap []int64
}

// NewCache allocates the power and offset buffers once.
func NewCache() *Cache {
	return &Cache{
		Pow:  make([]int64, castJMax+1),
		Trap: make([]int64, castJMax+1),
	}
}

// Load fills q^j and U_j(q) at every time from zero through castJMax.
// The empty power is 1 and the empty sum is 0, including q = 0.
func (c *Cache) Load(q int64) {
	pow := int64(1)
	trap := int64(0)
	ps := c.Pow[:len(c.Pow)]
	ts := c.Trap[:len(c.Trap)]
	for j := 0; j < len(ps); j++ {
		ps[j] = pow
		ts[j] = trap
		trap += pow
		pow *= q
	}
}

// PowInt returns q^j for a nonnegative exponent on the stated grid.
func PowInt(q int64, j int) int64 {
	out := int64(1)
	for i := 0; i < j; i++ {
		out *= q
	}
	return out
}

// TrapSum returns U_j(q), the sum of q^0 through q^(j-1). The empty sum is 0.
func TrapSum(q int64, j int) int64 {
	sum := int64(0)
	pow := int64(1)
	for i := 0; i < j; i++ {
		sum += pow
		pow *= q
	}
	return sum
}

// AffineValue returns q^j*n + c*U_j(q) by exact int64 arithmetic.
func AffineValue(q, c, n int64, j int) int64 {
	return PowInt(q, j)*n + c*TrapSum(q, j)
}

// AbsInt returns the absolute value of a signed integer on this grid.
func AbsInt(n int64) int64 {
	if n < 0 {
		return -n
	}
	return n
}

// Divides reports that D divides n. A nonzero divisor divides n when the
// remainder is zero. Go's remainder has the sign of the dividend and is zero
// exactly on multiples, including negative divisors. The zero divisor is not
// on the stated grid; it divides only zero.
func Divides(D, n int64) bool {
	if D == 0 {
		return n == 0
	}
	return n%D == 0
}

// Residue returns the representative of n in the half-open interval [0, m).
// The modulus m is positive on every call from the stated grid.
func Residue(n, m int64) int64 {
	v := n % m
	if v < 0 {
		v += m
	}
	return v
}

// ResidueStep applies one residue step r |-> q*r+c and reduces modulo m.
func ResidueStep(q, c, m, r int64) int64 {
	return Residue(q*r+c, m)
}

// ResidueWalk returns the j-th iterate of the residue step, starting at n.
func ResidueWalk(q, c, m, n int64, j int) int64 {
	r := Residue(n, m)
	for i := 0; i < j; i++ {
		r = ResidueStep(q, c, m, r)
	}
	return r
}

// CastAgrees reports that the affine residue equals the residue walk.
// It is false when |D| < 2, which is outside every parameter record.
func CastAgrees(q, c, D, n int64, j int) bool {
	m := AbsInt(D)
	if m < 2 || j < 0 {
		return false
	}
	return Residue(AffineValue(q, c, n, j), m) == ResidueWalk(q, c, m, n, j)
}

// CastIs reports that both the affine residue and the residue walk equal the
// supplied class. A class outside [0, |D|) is rejected, as is |D| < 2.
func CastIs(q, c, D, n int64, j int, claimed int64) bool {
	m := AbsInt(D)
	if m < 2 || j < 0 || claimed < 0 || claimed >= m {
		return false
	}
	if Residue(AffineValue(q, c, n, j), m) != claimed {
		return false
	}
	return ResidueWalk(q, c, m, n, j) == claimed
}

// IsFirstHit reports that D divides the affine state at time j and at no
// earlier time. It is false when |D| < 2.
func IsFirstHit(q, c, D, n int64, j int) bool {
	if j < 0 || AbsInt(D) < 2 {
		return false
	}
	for i := 0; i < j; i++ {
		if Divides(D, AffineValue(q, c, n, i)) {
			return false
		}
	}
	return Divides(D, AffineValue(q, c, n, j))
}

// CastDomainSize is the number of tuples (q, c, D, n, j) on the stated grid.
func CastDomainSize() uint64 {
	qCount := uint64(2*castQAbs + 1)
	cCount := uint64(2*castCAbs + 1)
	nCount := uint64(2*castNAbs + 1)
	dCount := uint64(2 * (castDMax - castDMin + 1))
	jCount := uint64(castJMax + 1)
	return qCount * cCount * nCount * dCount * jCount
}

// ChecksPerPoint is the number of comparisons recorded at one grid tuple.
// They are: the cast of n, the cast of n+D, agreement of CastIs with the
// walk, rejection of the next class, divisibility against the zero class,
// the first-hit criterion, and agreement of the shifted first hit.
func ChecksPerPoint() uint64 {
	return 7
}

// SweepDivisor checks one signed divisor for every seed and time.
// pow and trap are the buffers already loaded for q, sliced to their length.
func SweepDivisor(q, c, D int64, pow, trap []int64, t *Totals) {
	m := AbsInt(D)
	ps := pow[:len(pow)]
	ts := trap[:len(trap)]
	for n := int64(-castNAbs); n <= castNAbs; n++ {
		shift := n + D
		res := Residue(n, m)
		resShift := Residue(shift, m)
		earlier := false
		for j := 0; j <= castJMax; j++ {
			aff := ps[j]*n + c*ts[j]
			affShift := ps[j]*shift + c*ts[j]
			class := Residue(aff, m)
			classShift := Residue(affShift, m)
			// The affine class equals the walk, for both the seed and n+D.
			t.Check(class == res)
			t.Check(classShift == resShift)
			t.Check(CastIs(q, c, D, n, j, res))
			next := res + 1
			if next == m {
				next = 0
			}
			// The next class is a different residue, since m >= 2.
			t.Check(!CastIs(q, c, D, n, j, next))
			t.Check(Divides(D, aff) == (class == 0))
			resFirst := res == 0 && !earlier
			hit := IsFirstHit(q, c, D, n, j)
			t.Check(hit == resFirst)
			t.Check(IsFirstHit(q, c, D, shift, j) == hit)
			if res == 0 {
				earlier = true
			}
			res = ResidueStep(q, c, m, res)
			resShift = ResidueStep(q, c, m, resShift)
		}
	}
}

// SweepQ checks one multiplier on the whole coefficient, divisor, seed, and
// time grid. The cache is reused and is private to the calling worker.
func SweepQ(q int64, cache *Cache) Totals {
	cache.Load(q)
	var t Totals
	ps := cache.Pow[:len(cache.Pow)]
	ts := cache.Trap[:len(cache.Trap)]
	for c := int64(-castCAbs); c <= castCAbs; c++ {
		for absD := int64(castDMin); absD <= castDMax; absD++ {
			SweepDivisor(q, c, absD, ps, ts, &t)
			SweepDivisor(q, c, -absD, ps, ts, &t)
		}
	}
	return t
}

// RunCastSweep splits the multiplier range across workers and sums totals.
func RunCastSweep() Totals {
	qs := make([]int64, 0, 2*castQAbs+1)
	for q := int64(-castQAbs); q <= castQAbs; q++ {
		qs = append(qs, q)
	}
	parts := make([]Totals, len(qs))
	var wg sync.WaitGroup
	for worker := 0; worker < castWorkers; worker++ {
		wg.Add(1)
		go func(worker int) {
			defer wg.Done()
			cache := NewCache()
			for i := worker; i < len(qs); i += castWorkers {
				parts[i] = SweepQ(qs[i], cache)
			}
		}(worker)
	}
	wg.Wait()
	var total Totals
	for _, part := range parts {
		total.Add(part)
	}
	return total
}

// main prints the number of comparisons and exits nonzero on a disagreement.
func main() {
	total := RunCastSweep()
	fmt.Printf("residue checks: %d, failures: %d\n", total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
