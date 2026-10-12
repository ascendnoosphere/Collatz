// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"fmt"
	"math/big"
	"sync"
)

// These limits constrain finite certificate execution, not the mathematical theorem.
const MaxPhaseCount = 8
const BufferBits = 2048
const MaxSeedBits = 512

// Workspace owns coefficient certificates, cached phase increments, and replay storage.
type Workspace struct {
	base, rebased, residual, carried, q, c, d big.Int
	normalizedQ, normalizedC, normalizedD     big.Int
	current, next, quotient, remainder        big.Int
	cycleStart, expected, absStart, absState  big.Int
	orderTemp, orderQuotient, orderRemainder  big.Int
	exponent, power, lower, one               big.Int
	betas, phasePowers                        [MaxPhaseCount]big.Int
	u, v, gcd                                 int
}

// Gcd computes the scalar exponent gcd independently of the power reconstruction.
func Gcd(a, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// Reserve retains a signed integer while allocating limb storage before seed replay.
func Reserve(value, storage *big.Int) {
	var saved big.Int
	saved.Set(value)
	value.Set(storage)
	value.Set(&saved)
}

// Configure reconstructs the original coefficients and caches every rebased phase.
func Configure(workspace *Workspace, t, u, v, a, s int) error {
	if workspace == nil || t < 2 || t > 9 || u <= 0 || u > MaxPhaseCount ||
		v <= 0 || v > MaxPhaseCount ||
		a < u+v || a > 256 || s == 0 || s < -8 || s > 8 {
		return fmt.Errorf("parameters outside bounded arbitrary-exponent contract")
	}
	workspace.gcd = Gcd(u, v)
	workspace.u, workspace.v = u/workspace.gcd, v/workspace.gcd
	workspace.base.SetInt64(int64(t))
	workspace.residual.SetInt64(int64(s))
	workspace.one.SetInt64(1)
	workspace.exponent.SetInt64(int64(u))
	workspace.q.Exp(&workspace.base, &workspace.exponent, nil)
	workspace.exponent.SetInt64(int64(v))
	workspace.d.Exp(&workspace.base, &workspace.exponent, nil)
	workspace.exponent.SetInt64(int64(a))
	workspace.power.Exp(&workspace.base, &workspace.exponent, nil)
	workspace.c.Mul(&workspace.power, &workspace.residual)
	workspace.exponent.SetInt64(int64(workspace.gcd))
	workspace.rebased.Exp(&workspace.base, &workspace.exponent, nil)
	workspace.exponent.SetInt64(int64(a % workspace.gcd))
	workspace.power.Exp(&workspace.base, &workspace.exponent, nil)
	workspace.carried.Mul(&workspace.power, &workspace.residual)
	workspace.exponent.SetInt64(int64(workspace.u))
	workspace.normalizedQ.Exp(&workspace.rebased, &workspace.exponent, nil)
	workspace.exponent.SetInt64(int64(workspace.v))
	workspace.normalizedD.Exp(&workspace.rebased, &workspace.exponent, nil)
	workspace.exponent.SetInt64(int64(a / workspace.gcd))
	workspace.power.Exp(&workspace.rebased, &workspace.exponent, nil)
	workspace.normalizedC.Mul(&workspace.power, &workspace.carried)
	if workspace.q.Cmp(&workspace.normalizedQ) != 0 ||
		workspace.d.Cmp(&workspace.normalizedD) != 0 ||
		workspace.c.Cmp(&workspace.normalizedC) != 0 {
		return fmt.Errorf("coefficient reconstruction mismatch")
	}

	// Build the geometric sum without division by the possibly large base minus one.
	workspace.lower.SetInt64(0)
	workspace.power.SetInt64(1)
	for k := 0; k < workspace.v; k++ {
		workspace.phasePowers[k].Set(&workspace.power)
		workspace.lower.Add(&workspace.lower, &workspace.power)
		workspace.next.Mul(&workspace.power, &workspace.rebased)
		workspace.power.Set(&workspace.next)
	}
	for k := 0; k < workspace.v; k++ {
		e := a/workspace.gcd - workspace.u - workspace.v + 1 + k
		workspace.exponent.SetInt64(int64(e))
		workspace.power.Exp(&workspace.rebased, &workspace.exponent, nil)
		workspace.betas[k].Mul(&workspace.carried, &workspace.power)
		workspace.betas[k].Mul(&workspace.betas[k], &workspace.lower)
	}

	// At most sixteen affine updates and the contracted input sizes fit this reserve.
	var storage big.Int
	storage.SetBit(&storage, BufferBits, 1)
	for _, value := range []*big.Int{
		&workspace.current, &workspace.next, &workspace.quotient, &workspace.remainder,
		&workspace.cycleStart, &workspace.expected, &workspace.absStart, &workspace.absState,
		&workspace.orderTemp, &workspace.orderQuotient, &workspace.orderRemainder,
		&workspace.lower,
	} {
		Reserve(value, &storage)
	}
	return nil
}

// WholeOrder extracts whole-base order without interpreting a composite base as prime.
func WholeOrder(workspace *Workspace) int {
	workspace.orderTemp.Set(&workspace.current)
	k := 0
	for {
		workspace.orderQuotient.QuoRem(&workspace.orderTemp, &workspace.rebased,
			&workspace.orderRemainder)
		if workspace.orderRemainder.Sign() != 0 {
			return k
		}
		workspace.orderTemp.Set(&workspace.orderQuotient)
		k++
	}
}

// ApplyRawStep gives division priority and uses disjoint affine multiplication buffers.
func ApplyRawStep(workspace *Workspace) bool {
	workspace.quotient.QuoRem(&workspace.current, &workspace.d, &workspace.remainder)
	if workspace.remainder.Sign() == 0 {
		workspace.current.Set(&workspace.quotient)
		return true
	}
	workspace.next.Mul(&workspace.q, &workspace.current)
	workspace.next.Add(&workspace.next, &workspace.c)
	workspace.current, workspace.next = workspace.next, workspace.current
	return false
}

// CheckSeed independently replays two full raw sweeps, including all intermediate guards.
func CheckSeed(workspace *Workspace, seed *big.Int) error {
	if workspace == nil || workspace.u <= 0 || seed == nil || seed.Sign() == 0 ||
		seed.BitLen() > MaxSeedBits {
		return fmt.Errorf("seed outside bounded arbitrary-exponent contract")
	}
	workspace.current.Set(seed)
	// Only legal initial divisions are removed; magnitude strictly decreases each time.
	for {
		workspace.quotient.QuoRem(&workspace.current, &workspace.d, &workspace.remainder)
		if workspace.remainder.Sign() != 0 {
			break
		}
		workspace.current.Set(&workspace.quotient)
	}
	k := WholeOrder(workspace)
	if k >= workspace.v {
		return fmt.Errorf("initial normalization phase mismatch")
	}
	// Return equality alone does not certify the raw branch counts or intermediate bounds.
	for rotation := 0; rotation < 2; rotation++ {
		workspace.cycleStart.Set(&workspace.current)
		workspace.expected.Add(&workspace.cycleStart, &workspace.betas[k])
		workspace.absStart.Abs(&workspace.cycleStart)
		// Do not extend the magnitude estimate across an opposite-sign initial segment.
		aligned := workspace.cycleStart.Sign() == workspace.c.Sign()
		affines, divisions := 0, 0
		for step := 0; step < workspace.u+workspace.v; step++ {
			if ApplyRawStep(workspace) {
				divisions++
			} else {
				affines++
			}
			if workspace.current.Sign() == 0 {
				return fmt.Errorf("nonzero orbit reached zero")
			}
			if aligned {
				workspace.absState.Abs(&workspace.current)
				workspace.lower.Mul(&workspace.phasePowers[k], &workspace.absState)
				if workspace.lower.Cmp(&workspace.absStart) < 0 {
					return fmt.Errorf("aligned intermediate magnitude mismatch")
				}
			}
		}
		if workspace.current.Cmp(&workspace.expected) != 0 || affines != workspace.v ||
			divisions != workspace.u || WholeOrder(workspace) != k {
			return fmt.Errorf("raw sweep, clock, or phase mismatch")
		}
	}
	return nil
}

// CheckBase exhausts a bounded base slice with no exponent-ordering or gcd restriction.
func CheckBase(t int, cases *int, failure *error) {
	var workspace Workspace
	var seed, nextSeed, seedStorage big.Int
	seedStorage.SetBit(&seedStorage, MaxSeedBits, 1)
	Reserve(&seed, &seedStorage)
	Reserve(&nextSeed, &seedStorage)
	for v := 1; v <= MaxPhaseCount; v++ {
		for u := 1; u <= MaxPhaseCount; u++ {
			for a := u + v; a <= u+v+2; a++ {
				for s := -8; s <= 8; s++ {
					if s == 0 {
						continue
					}
					if err := Configure(&workspace, t, u, v, a, s); err != nil {
						*failure = err
						return
					}
					for n := -128; n <= 128; n++ {
						if n == 0 {
							continue
						}
						seed.SetInt64(int64(n))
						if err := CheckSeed(&workspace, &seed); err != nil {
							*failure = err
							return
						}
						*cases++
					}
					// Forced phases retain composite nonunit residues as separate controls.
					for k := 0; k < workspace.v; k++ {
						for w := -8; w <= 8; w++ {
							if w == 0 || int64(w)%workspace.rebased.Int64() == 0 {
								continue
							}
							seed.SetInt64(int64(w))
							nextSeed.Mul(&seed, &workspace.phasePowers[k])
							seed.Set(&nextSeed)
							if err := CheckSeed(&workspace, &seed); err != nil {
								*failure = err
								return
							}
							*cases++
						}
					}
				}
			}
		}
	}
}

// main assigns each base slice its own workspace and reports finite certificates only.
func main() {
	var counts [8]int
	var failures [8]error
	var group sync.WaitGroup
	for i := range counts {
		group.Add(1)
		go func(i int) {
			defer group.Done()
			CheckBase(i+2, &counts[i], &failures[i])
		}(i)
	}
	group.Wait()
	total := 0
	for i := range counts {
		if failures[i] != nil {
			panic(failures[i])
		}
		total += counts[i]
	}
	fmt.Printf("%d bounded arbitrary-exponent two-sweep certificates checked\n", total)
}
