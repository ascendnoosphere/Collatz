// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"fmt"
	"math/big"
	"sync"
)

// These limits constrain the replay program, not the quantified absorption theorems.
const (
	MaxSeedBits        = 512
	MaxCoefficientBits = 512
	MaxPeelSteps       = 512
	MaxRawPrefix       = 4096
	TailSteps          = 16
	StorageBits        = 8192
)

// Cache holds cold certificate construction buffers separately from raw replay state.
type Cache struct {
	qAbs, cAbs, dAbs, sigma, remaining, gcd, quotient        big.Int
	product, power, exponent, coreOffset, remainder, storage big.Int
}

// Workspace owns disjoint raw/core operands and one validated immutable coefficient tuple.
type Workspace struct {
	q, c, d, sigma, coreOffset                                         big.Int
	raw, rawNext, core, coreNext, quotient, remainder, product, scaled big.Int
	startRaw, startCore, minimum, cutoff                               big.Int
	cache                                                              Cache
	steps                                                              int
	automatic, configured, reserved                                    bool
}

// Reserve gives an operand independent capacity before any seed or phase loop.
func Reserve(value, storage *big.Int) {
	storage.SetBit(storage, StorageBits-1, 1)
	value.Set(storage)
	value.SetInt64(0)
}

// Prepare allocates every owned buffer once; later configurations reuse those buffers.
func Prepare(workspace *Workspace) {
	if workspace.reserved {
		return
	}
	cache := &workspace.cache
	values := []*big.Int{
		&workspace.q, &workspace.c, &workspace.d, &workspace.sigma,
		&workspace.coreOffset, &workspace.raw, &workspace.rawNext, &workspace.core,
		&workspace.coreNext, &workspace.quotient, &workspace.remainder,
		&workspace.product, &workspace.scaled, &workspace.startRaw, &workspace.startCore,
		&workspace.minimum, &workspace.cutoff, &cache.qAbs, &cache.cAbs, &cache.dAbs,
		&cache.sigma, &cache.remaining, &cache.gcd, &cache.quotient, &cache.product,
		&cache.power, &cache.exponent, &cache.coreOffset, &cache.remainder,
	}
	for _, value := range values {
		Reserve(value, &cache.storage)
	}
	workspace.reserved = true
}

// Configure constructs a gcd-only power certificate before changing the validated tuple.
// A nil factor selects maximal extraction under gcd(C,D)=1; otherwise the supplied factor
// needs only gcd(factor,D)=1, factor|C and multiplier-supported primes.
func Configure(workspace *Workspace, q, c, d, factor *big.Int) error {
	if workspace == nil || q == nil || c == nil || d == nil {
		return fmt.Errorf("nil configuration")
	}
	if q.BitLen() > 8 || !q.IsInt64() || q.Int64() < -181 || q.Int64() > 181 ||
		c.Sign() == 0 || c.BitLen() > MaxCoefficientBits || !d.IsInt64() ||
		d.Int64() < -32 || d.Int64() > 32 ||
		(d.Int64() > -2 && d.Int64() < 2) {
		return fmt.Errorf("configuration outside finite coefficient bounds")
	}
	if factor != nil && (factor.Sign() <= 0 || factor.BitLen() > MaxCoefficientBits) {
		return fmt.Errorf("factor outside positive finite bounds")
	}
	Prepare(workspace)
	cache := &workspace.cache
	cache.qAbs.Abs(q)
	cache.cAbs.Abs(c)
	cache.dAbs.Abs(d)
	if factor == nil {
		cache.gcd.GCD(nil, nil, &cache.cAbs, &cache.dAbs)
		if cache.gcd.Cmp(big.NewInt(1)) != 0 {
			return fmt.Errorf("automatic extraction requires gcd(C,D)=1")
		}
		cache.remaining.Set(&cache.cAbs)
	} else {
		cache.quotient.QuoRem(c, factor, &cache.remainder)
		if cache.remainder.Sign() != 0 {
			return fmt.Errorf("supplied factor does not divide offset")
		}
		cache.remaining.Set(factor)
	}
	cache.sigma.SetInt64(1)
	steps := 0
	for {
		cache.gcd.GCD(nil, nil, &cache.remaining, &cache.qAbs)
		if cache.gcd.Cmp(big.NewInt(1)) == 0 {
			break
		}
		if steps == MaxPeelSteps {
			return fmt.Errorf("gcd extraction exceeded finite step bound")
		}
		cache.product.Mul(&cache.sigma, &cache.gcd)
		cache.sigma.Set(&cache.product)
		cache.quotient.QuoRem(&cache.remaining, &cache.gcd, &cache.remainder)
		if cache.remainder.Sign() != 0 {
			return fmt.Errorf("inexact gcd division")
		}
		cache.remaining.Set(&cache.quotient)
		steps++
	}
	if factor != nil && cache.remaining.Cmp(big.NewInt(1)) != 0 {
		return fmt.Errorf("supplied factor has unsupported prime")
	}
	cache.gcd.GCD(nil, nil, &cache.sigma, &cache.dAbs)
	if cache.gcd.Cmp(big.NewInt(1)) != 0 {
		return fmt.Errorf("factor is not coprime to raw divisor")
	}
	cache.coreOffset.QuoRem(c, &cache.sigma, &cache.remainder)
	if cache.remainder.Sign() != 0 {
		return fmt.Errorf("extracted factor does not divide offset")
	}
	cache.exponent.SetInt64(int64(steps))
	cache.power.Exp(q, &cache.exponent, nil)
	cache.remainder.Mod(&cache.power, &cache.sigma)
	if cache.remainder.Sign() != 0 {
		return fmt.Errorf("gcd power certificate failed")
	}
	cache.product.Mul(&cache.sigma, &cache.coreOffset)
	if cache.product.Cmp(c) != 0 {
		return fmt.Errorf("offset reconstruction failed")
	}
	workspace.q.Set(q)
	workspace.c.Set(c)
	workspace.d.Set(d)
	workspace.sigma.Set(&cache.sigma)
	workspace.coreOffset.Set(&cache.coreOffset)
	workspace.steps = steps
	workspace.automatic = factor == nil
	workspace.configured = true
	return nil
}

// Step performs division only on an exactly divisible state; both branch outputs are disjoint.
func Step(state, q, c, d, next *big.Int, workspace *Workspace) bool {
	workspace.quotient.QuoRem(state, d, &workspace.remainder)
	if workspace.remainder.Sign() == 0 {
		next.Set(&workspace.quotient)
		return true
	}
	workspace.product.Mul(q, state)
	next.Add(&workspace.product, c)
	return false
}

// CheckSeed finds one entry witness, checks its affine budget and replays one common raw tail.
// Prefix exhaustion is a bounded replay refusal, never nonabsorption or escape.
func CheckSeed(workspace *Workspace, seed *big.Int) error {
	if workspace == nil || !workspace.configured || seed == nil ||
		seed.BitLen() > MaxSeedBits {
		return fmt.Errorf("seed outside configured finite domain")
	}
	workspace.raw.Set(seed)
	affines := 0
	for t := 0; ; t++ {
		workspace.quotient.QuoRem(&workspace.raw, &workspace.sigma, &workspace.remainder)
		if workspace.remainder.Sign() == 0 {
			break
		}
		if t == MaxRawPrefix {
			return fmt.Errorf("entry prefix exceeded finite replay bound")
		}
		divided := Step(&workspace.raw, &workspace.q, &workspace.c, &workspace.d,
			&workspace.rawNext, workspace)
		if !divided {
			affines++
		}
		if affines > workspace.steps {
			return fmt.Errorf("affine entry budget failed")
		}
		workspace.raw.Set(&workspace.rawNext)
	}
	workspace.core.QuoRem(&workspace.raw, &workspace.sigma, &workspace.remainder)
	if workspace.remainder.Sign() != 0 {
		return fmt.Errorf("entry quotient was not exact")
	}
	for r := 0; r <= TailSteps; r++ {
		workspace.scaled.Mul(&workspace.sigma, &workspace.core)
		if workspace.scaled.Cmp(&workspace.raw) != 0 {
			return fmt.Errorf("raw tail state reconstruction failed")
		}
		if r == TailSteps {
			break
		}
		rawDivision := Step(&workspace.raw, &workspace.q, &workspace.c, &workspace.d,
			&workspace.rawNext, workspace)
		coreDivision := Step(&workspace.core, &workspace.q, &workspace.coreOffset,
			&workspace.d, &workspace.coreNext, workspace)
		if rawDivision != coreDivision {
			return fmt.Errorf("raw complementary guard mismatch")
		}
		workspace.raw.Set(&workspace.rawNext)
		workspace.core.Set(&workspace.coreNext)
	}
	return nil
}

// CheckCycle checks every shorter return and every raw phase of a prescribed lifted cycle.
func CheckCycle(workspace *Workspace, coreSeed *big.Int, period int) error {
	if workspace == nil || !workspace.configured || coreSeed == nil ||
		coreSeed.BitLen() > MaxSeedBits || period <= 0 || period > 64 {
		return fmt.Errorf("cycle outside finite certificate domain")
	}
	workspace.startCore.Set(coreSeed)
	workspace.startRaw.Mul(&workspace.sigma, coreSeed)
	workspace.core.Set(&workspace.startCore)
	workspace.raw.Set(&workspace.startRaw)
	workspace.minimum.Set(&workspace.raw)
	for r := 1; r <= period; r++ {
		rawDivision := Step(&workspace.raw, &workspace.q, &workspace.c, &workspace.d,
			&workspace.rawNext, workspace)
		coreDivision := Step(&workspace.core, &workspace.q, &workspace.coreOffset,
			&workspace.d, &workspace.coreNext, workspace)
		workspace.raw.Set(&workspace.rawNext)
		workspace.core.Set(&workspace.coreNext)
		workspace.scaled.Mul(&workspace.sigma, &workspace.core)
		if rawDivision != coreDivision || workspace.scaled.Cmp(&workspace.raw) != 0 {
			return fmt.Errorf("cycle phase or guard reconstruction failed")
		}
		if workspace.raw.Cmp(&workspace.minimum) < 0 {
			workspace.minimum.Set(&workspace.raw)
		}
		rawReturn := workspace.raw.Cmp(&workspace.startRaw) == 0
		coreReturn := workspace.core.Cmp(&workspace.startCore) == 0
		if rawReturn != coreReturn || (r < period && rawReturn) ||
			(r == period && !rawReturn) {
			return fmt.Errorf("primitive raw return certificate failed")
		}
	}
	return nil
}

// SearchCutoff computes the exact natural ceiling, including the zero cutoff boundary.
func SearchCutoff(workspace *Workspace, minimum *big.Int) error {
	if workspace == nil || !workspace.configured || minimum == nil ||
		minimum.Sign() < 0 || minimum.BitLen() > MaxSeedBits {
		return fmt.Errorf("minimum outside finite cutoff domain")
	}
	workspace.product.Add(minimum, &workspace.sigma)
	workspace.product.Sub(&workspace.product, big.NewInt(1))
	workspace.cutoff.Quo(&workspace.product, &workspace.sigma)
	return nil
}

// Gcd is used only on the small nonnegative dataset coefficients.
func Gcd(a, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// CheckChunk gives one owner to each workspace and one output slot to each independent chunk.
func CheckChunk(chunk int, count *uint64, failure *error) {
	var workspace Workspace
	var q, c, d, seed big.Int
	Prepare(&workspace)
	Reserve(&seed, &workspace.cache.storage)
	for qIndex := chunk; qIndex < 15; qIndex += 8 {
		q.SetInt64(int64(qIndex - 7))
		for magnitude := 1; magnitude <= 32; magnitude++ {
			for divisor := 2; divisor <= 8; divisor++ {
				if Gcd(magnitude, divisor) != 1 {
					continue
				}
				for _, cSign := range [2]int64{-1, 1} {
					c.SetInt64(cSign * int64(magnitude))
					for _, dSign := range [2]int64{-1, 1} {
						d.SetInt64(dSign * int64(divisor))
						if err := Configure(&workspace, &q, &c, &d, nil); err != nil {
							*failure = err
							return
						}
						for n := -64; n <= 64; n++ {
							seed.SetInt64(int64(n))
							if err := CheckSeed(&workspace, &seed); err != nil {
								*failure = fmt.Errorf("q=%s c=%s d=%s n=%d: %w",
									&q, &c, &d, n, err)
								return
							}
							*count++
						}
					}
				}
			}
		}
	}
}

// main reports finite seed/parameter certificates; their count is not an infinite orbit census.
func main() {
	var counts [8]uint64
	var failures [8]error
	var wait sync.WaitGroup
	for chunk := range counts {
		wait.Add(1)
		go func(index int) {
			defer wait.Done()
			CheckChunk(index, &counts[index], &failures[index])
		}(chunk)
	}
	wait.Wait()
	var total uint64
	for index, err := range failures {
		if err != nil {
			panic(fmt.Sprintf("chunk %d: %v", index, err))
		}
		total += counts[index]
	}
	fmt.Printf("supported-offset raw-tail certificates: %d\n", total)
}
