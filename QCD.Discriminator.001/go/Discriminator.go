// SPDX-License-Identifier: CC-BY-4.0
// Exact return and escape checks for D = q^k and c = tD.
package main

import (
	"errors"
	"fmt"
	"sync"
)

const (
	MaxQ        uint64 = 8
	MaxK        uint64 = 4
	MaxT        uint64 = 8
	MaxSeed     uint64 = 256
	MaxBlocks   uint64 = 8
	MaxRawTicks uint64 = 64
)

// Witness specifies a positive seed of the neutral family.
type Witness struct{ Q, K, T, N uint64 }

// ReturnEval records both orbit clocks and the comparison threshold.
type ReturnEval struct{ Delay, State, Clip, J, Excess, Floor, Clock uint64 }

// Workspace reuses the raw state without allocating during successful checks.
type Workspace struct{ state uint64 }

// Cache holds the exact derived parameters of one bounded family.
type Cache struct{ q, k, t, d, c, b, g, excess, floor uint64 }

// Census counts the checked seeds and scalar comparisons in one q chunk.
type Census struct {
	Seeds, Escape, Return, Comparisons int
	Err                                error
}

// Mul rejects an unsigned product that would overflow.
func Mul(a, b uint64) (uint64, error) {
	if a != 0 && b > ^uint64(0)/a {
		return 0, errors.New("product exceeds 64 bits")
	}
	return a * b, nil
}

// Add rejects an unsigned sum that would overflow.
func Add(a, b uint64) (uint64, error) {
	if a > ^uint64(0)-b {
		return 0, errors.New("sum exceeds 64 bits")
	}
	return a + b, nil
}

// Sub preserves the mathematical nonnegative-difference contract.
func Sub(a, b uint64) (uint64, error) {
	if a < b {
		return 0, errors.New("difference is negative")
	}
	return a - b, nil
}

// Pow handles constant bases before bounding the number of multiplications.
func Pow(q, k uint64) (uint64, error) {
	if k == 0 || q == 1 {
		return 1, nil
	}
	if q == 0 {
		return 0, nil
	}
	if k >= 64 {
		return 0, errors.New("power exceeds 64 bits")
	}
	out := uint64(1)
	for i := uint64(0); i < k; i++ {
		var err error
		out, err = Mul(out, q)
		if err != nil {
			return 0, err
		}
	}
	return out, nil
}

// Geom uses qG+1, avoiding the unnecessary final power q^j.
func Geom(q, j uint64) (uint64, error) {
	if j == 0 || q == 1 {
		return j, nil
	}
	if q == 0 {
		return 1, nil
	}
	if j > 64 {
		return 0, errors.New("geometric sum exceeds 64 bits")
	}
	sum := uint64(0)
	for i := uint64(0); i < j; i++ {
		product, err := Mul(q, sum)
		if err != nil {
			return 0, err
		}
		sum, err = Add(product, 1)
		if err != nil {
			return 0, err
		}
	}
	return sum, nil
}

// Gcd is Euclid's algorithm, with Gcd(0,0) equal to zero.
func Gcd(a, b uint64) uint64 {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// NewCache validates the finite parameter budget before evaluating any power.
func NewCache(q, k, t uint64) (Cache, error) {
	var out Cache
	if q < 2 || q > MaxQ || k < 1 || k > MaxK || t < 1 || t > MaxT {
		return out, errors.New("family outside the finite parameter budget")
	}
	d, err := Pow(q, k)
	if err != nil {
		return out, err
	}
	c, err := Mul(t, d)
	if err != nil {
		return out, err
	}
	sum, err := Geom(q, k)
	if err != nil {
		return out, err
	}
	b, err := Mul(t, sum)
	if err != nil {
		return out, err
	}
	g := Gcd(q, t)
	scaled, err := Mul(q/g, b)
	if err != nil {
		return out, err
	}
	excess, err := Sub(scaled, t)
	if err != nil {
		return out, err
	}
	return Cache{q, k, t, d, c, b, g, excess, excess / (q - 1)}, nil
}

// RawStep rejects invalid divisors and checks the full affine arithmetic.
func RawStep(q, c, d, n uint64) (uint64, error) {
	if q == 0 || c == 0 || d < 2 {
		return 0, errors.New("invalid raw-map parameters")
	}
	if n%d == 0 {
		return n / d, nil
	}
	qn, err := Mul(q, n)
	if err != nil {
		return 0, err
	}
	return Add(qn, c)
}

// Iterate enforces a tick budget even when the raw state would be periodic.
func (ws *Workspace) Iterate(q, c, d, steps, n uint64) (uint64, error) {
	if ws == nil || steps > MaxRawTicks || q == 0 || c == 0 || d < 2 {
		return 0, errors.New("invalid workspace, raw parameters, or tick budget")
	}
	ws.state = n
	for i := uint64(0); i < steps; i++ {
		next, err := RawStep(q, c, d, ws.state)
		if err != nil {
			return 0, err
		}
		ws.state = next
	}
	return ws.state, nil
}

// Clip removes successive q factors, including the capped valuation of zero.
func Clip(q, k, n uint64) (uint64, error) {
	if q < 2 || k >= 64 {
		return 0, errors.New("invalid base or clip budget")
	}
	j := uint64(0)
	for j < k && n%q == 0 {
		n /= q
		j++
	}
	return j, nil
}

// ValidateSeed keeps seed bounds separate from the mathematical gcd split.
func ValidateSeed(w Witness, ws *Workspace) (Cache, error) {
	if ws == nil || w.N < 1 || w.N > MaxSeed {
		return Cache{}, errors.New("invalid workspace or seed budget")
	}
	cache, err := NewCache(w.Q, w.K, w.T)
	if err != nil {
		return Cache{}, err
	}
	if w.N%w.Q == 0 {
		return Cache{}, errors.New("seed is divisible by q")
	}
	return cache, nil
}

// CheckEscape compares every partial state in nine neutral blocks.
func CheckEscape(w Witness, ws *Workspace) (int, error) {
	cache, err := ValidateSeed(w, ws)
	if err != nil {
		return 0, err
	}
	if w.N%cache.g == 0 {
		return 0, errors.New("gcd meets an escape seed")
	}
	checks := 0
	// The budget bounds every intermediate state by 4096*(256+9*4680) < 2^28.
	for s := uint64(0); s <= MaxBlocks; s++ {
		anchor := w.N + s*cache.b
		for i := uint64(0); i <= w.K; i++ {
			got, err := ws.Iterate(w.Q, cache.c, cache.d, s*(w.K+1)+i, w.N)
			if err != nil {
				return 0, err
			}
			qi, _ := Pow(w.Q, i)
			gi, _ := Geom(w.Q, i)
			want := qi*anchor + cache.c*gi
			if got != want || got < anchor {
				return 0, errors.New("escape formula or all-clock bound failed")
			}
			checks++
		}
	}
	return checks, nil
}

// EvalReturn checks minimal delay, both raw landings, and the clipped formula.
func EvalReturn(w Witness, ws *Workspace) (ReturnEval, error) {
	var out ReturnEval
	cache, err := ValidateSeed(w, ws)
	if err != nil {
		return out, err
	}
	if w.N%cache.g != 0 {
		return out, errors.New("gcd misses a return seed")
	}
	// At most q/g-1 anchors are examined; the first hit is the least delay.
	s, m := uint64(1), uint64(0)
	for ; s < w.Q/cache.g; s++ {
		m = w.N + s*cache.b
		if m%w.Q == 0 {
			break
		}
	}
	if s == w.Q/cache.g {
		return out, errors.New("no delay in the proved range")
	}
	land, err := ws.Iterate(w.Q, cache.c, cache.d, s*(w.K+1), w.N)
	if err != nil || land != m {
		return out, errors.New("neutral block landing failed")
	}
	j, err := Clip(w.Q, w.K, m)
	if err != nil || j == 0 {
		return out, errors.New("clipped valuation missed q")
	}
	pj, _ := Pow(w.Q, j)
	tail, _ := Geom(w.Q, w.K-j)
	value := m/pj + w.T*tail
	clock := s*(w.K+1) + w.K - j + 1
	got, err := ws.Iterate(w.Q, cache.c, cache.d, clock, w.N)
	if err != nil || got != value || value == 0 {
		return out, errors.New("positive clipped raw return failed")
	}
	return ReturnEval{s, m, j, value, cache.excess, cache.floor, clock}, nil
}

// CheckReturn checks two raw landings and the product and floor inequalities.
func CheckReturn(w Witness, ws *Workspace) (int, error) {
	ev, err := EvalReturn(w, ws)
	if err != nil {
		return 0, err
	}
	if ev.J*w.Q > w.N+ev.Excess {
		return 0, errors.New("return product bound failed")
	}
	if (w.N > ev.Floor && ev.J >= w.N) || (w.N <= ev.Floor && ev.J > ev.Floor) {
		return 0, errors.New("return floor comparison failed")
	}
	return 4, nil
}

// ScanQ partitions the complete bounded parameter grid by q.
func ScanQ(q uint64) Census {
	var out Census
	if q < 2 || q > MaxQ {
		out.Err = errors.New("q outside the census budget")
		return out
	}
	ws := Workspace{}
	for k := uint64(1); k <= MaxK; k++ {
		for t := uint64(1); t <= MaxT; t++ {
			g := Gcd(q, t)
			for n := uint64(1); n <= MaxSeed; n++ {
				if n%q == 0 {
					continue
				}
				w := Witness{q, k, t, n}
				var count int
				if n%g != 0 {
					count, out.Err = CheckEscape(w, &ws)
					out.Escape++
				} else {
					count, out.Err = CheckReturn(w, &ws)
					out.Return++
				}
				if out.Err != nil {
					return out
				}
				out.Seeds++
				out.Comparisons += count
			}
		}
	}
	return out
}

// main runs disjoint q chunks concurrently and reports them in parameter order.
func main() {
	var rows [7]Census
	var wg sync.WaitGroup
	for i := range rows {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			rows[i] = ScanQ(uint64(i) + 2)
		}(i)
	}
	wg.Wait()
	for i, row := range rows {
		if row.Err != nil {
			panic(row.Err)
		}
		fmt.Printf("q=%d seeds=%d escape=%d return=%d comparisons=%d\n",
			i+2, row.Seeds, row.Escape, row.Return, row.Comparisons)
	}
}
