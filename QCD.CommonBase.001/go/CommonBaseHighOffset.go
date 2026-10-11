// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"fmt"
	"math/big"
	"sync"
)

// These limits bound the finite certificate search, not the universal theorem.
const (
	MaxPhaseCount     = 8
	MaxBase           = 9
	MaxOffsetExponent = 256
	MaxOffsetResidual = 8
)

// Workspace reuses the exact state, division, order, and phase-translation buffers.
type Workspace struct {
	u, v, seedBits                         int
	configured                             bool
	base, q, c, d, geometric, divisorPower big.Int
	current, next, quotient, remainder     big.Int
	orderState, orderQuotient, orderRem    big.Int
	cycleStart, expected, lower, seed      big.Int
	absoluteStart, absoluteState           big.Int
	exponent, factor                       big.Int
	beta, phase                            [MaxPhaseCount]big.Int
}

// Gcd selects precisely the coprime phase-rotation parameters in the source family.
func Gcd(a, b int) int {
	for b != 0 {
		a, b = b, a%b
	}
	return a
}

// Configure refuses parameters outside the theorem or this checker's finite resource contract.
func Configure(workspace *Workspace, t, u, v, a, s int) error {
	if workspace == nil || t < 2 || t > MaxBase || u < 1 || u >= v ||
		v > MaxPhaseCount || Gcd(u, v) != 1 || a < u+v || a > MaxOffsetExponent ||
		s == 0 || s < -MaxOffsetResidual || s > MaxOffsetResidual {
		return fmt.Errorf("parameters outside the high-offset certificate contract")
	}
	workspace.u, workspace.v = u, v
	workspace.base.SetInt64(int64(t))
	workspace.exponent.SetInt64(int64(u))
	workspace.q.Exp(&workspace.base, &workspace.exponent, nil)
	workspace.exponent.SetInt64(int64(v))
	workspace.d.Exp(&workspace.base, &workspace.exponent, nil)
	workspace.exponent.SetInt64(int64(a))
	workspace.c.Exp(&workspace.base, &workspace.exponent, nil)
	workspace.factor.SetInt64(int64(s))
	workspace.c.Mul(&workspace.c, &workspace.factor)
	workspace.exponent.SetInt64(int64(u))
	workspace.divisorPower.Exp(&workspace.d, &workspace.exponent, nil)

	// Summing powers of the base, not of q, is the phase-permutation prediction.
	workspace.geometric.SetInt64(1)
	workspace.phase[0].SetInt64(1)
	for i := 1; i < v; i++ {
		workspace.phase[i].Mul(&workspace.phase[i-1], &workspace.base)
		workspace.geometric.Add(&workspace.geometric, &workspace.phase[i])
	}
	for k := 0; k < v; k++ {
		workspace.exponent.SetInt64(int64(a - u - v + 1 + k))
		workspace.beta[k].Exp(&workspace.base, &workspace.exponent, nil)
		workspace.beta[k].Mul(&workspace.beta[k], &workspace.geometric)
		workspace.beta[k].Mul(&workspace.beta[k], &workspace.factor)
	}
	workspace.seedBits = max(8, (v-1)*workspace.base.BitLen()+4)
	bits := 2*v*(workspace.q.BitLen()+1) + workspace.c.BitLen() +
		workspace.seedBits + workspace.divisorPower.BitLen() + 64
	PrepareStorage(workspace, bits)
	workspace.configured = true
	return nil
}

// PrepareStorage reserves conservative limb capacity for this bounded search.
func PrepareStorage(workspace *Workspace, bits int) {
	buffers := [...]*big.Int{
		&workspace.current, &workspace.next, &workspace.quotient, &workspace.remainder,
		&workspace.orderState, &workspace.orderQuotient, &workspace.orderRem,
		&workspace.cycleStart, &workspace.expected, &workspace.lower, &workspace.seed,
		&workspace.absoluteStart, &workspace.absoluteState, &workspace.factor,
	}
	for _, buffer := range buffers {
		buffer.SetBit(buffer, bits, 1)
		buffer.SetInt64(0)
	}
}

// ApplyAffine avoids multiplication into either input's backing storage.
func ApplyAffine(workspace *Workspace) {
	workspace.next.Mul(&workspace.q, &workspace.current)
	workspace.next.Add(&workspace.next, &workspace.c)
	workspace.current, workspace.next = workspace.next, workspace.current
}

// WholeOrder counts whole-base divisibility of a nonzero state, including composite bases.
func WholeOrder(workspace *Workspace) int {
	workspace.orderState.Set(&workspace.current)
	order := 0
	for {
		workspace.orderQuotient.QuoRem(
			&workspace.orderState, &workspace.base, &workspace.orderRem)
		if workspace.orderRem.Sign() != 0 {
			return order
		}
		workspace.orderState.Set(&workspace.orderQuotient)
		order++
	}
}

// CheckLowerBound applies only after the cycle start has the offset's sign.
func CheckLowerBound(workspace *Workspace) error {
	if workspace.cycleStart.Sign() != workspace.c.Sign() {
		return nil
	}
	if workspace.current.Sign() != workspace.c.Sign() {
		return fmt.Errorf("raw state lost the aligned sign")
	}
	workspace.absoluteState.Abs(&workspace.current)
	workspace.lower.Mul(&workspace.absoluteState, &workspace.divisorPower)
	workspace.absoluteStart.Abs(&workspace.cycleStart)
	if workspace.lower.Cmp(&workspace.absoluteStart) < 0 {
		return fmt.Errorf("raw state violates D^u magnitude lower bound")
	}
	return nil
}

// CheckSeed replays two legal rotations and verifies clock, phase, and translation.
func CheckSeed(workspace *Workspace, seed *big.Int, u, v int) error {
	if workspace == nil || !workspace.configured || seed == nil ||
		u != workspace.u || v != workspace.v {
		return fmt.Errorf("unconfigured workspace or mismatched rotation parameters")
	}
	if seed.BitLen() > workspace.seedBits {
		return fmt.Errorf("seed exceeds reserved certificate capacity")
	}
	workspace.current.Set(seed)
	if workspace.current.Sign() == 0 {
		return fmt.Errorf("zero is a separate fixed point")
	}

	// Initial divisions terminate at a nonzero state outside the division lattice.
	for {
		workspace.quotient.QuoRem(&workspace.current, &workspace.d, &workspace.remainder)
		if workspace.remainder.Sign() != 0 {
			break
		}
		workspace.current.Set(&workspace.quotient)
	}
	firstOrder := WholeOrder(workspace)
	if firstOrder >= v {
		return fmt.Errorf("initial normalization did not remove D divisibility")
	}

	for rotation := 0; rotation < 2; rotation++ {
		workspace.cycleStart.Set(&workspace.current)
		workspace.expected.Add(&workspace.cycleStart, &workspace.beta[firstOrder])
		divisions, clock := 0, 0
		order := firstOrder
		for event := 0; event < v; event++ {
			workspace.quotient.QuoRem(
				&workspace.current, &workspace.d, &workspace.remainder)
			if workspace.remainder.Sign() == 0 {
				return fmt.Errorf("affine event started on division lattice")
			}
			ApplyAffine(workspace)
			if workspace.current.Sign() == 0 {
				return fmt.Errorf("affine event unexpectedly reached zero")
			}
			clock++
			if err := CheckLowerBound(workspace); err != nil {
				return err
			}

			// The high-offset hypothesis permits exactly zero or one division here.
			blockDivisions := 0
			for {
				workspace.quotient.QuoRem(
					&workspace.current, &workspace.d, &workspace.remainder)
				if workspace.remainder.Sign() != 0 {
					break
				}
				workspace.current.Set(&workspace.quotient)
				blockDivisions++
				clock++
				if err := CheckLowerBound(workspace); err != nil {
					return err
				}
			}
			predictedDivisions := (order + u) / v
			if blockDivisions != predictedDivisions || blockDivisions > 1 {
				return fmt.Errorf("wrong event division count")
			}
			divisions += blockDivisions
			order = (order + u) % v
			if actual := WholeOrder(workspace); actual != order {
				return fmt.Errorf("whole-base order %d, expected %d", actual, order)
			}
		}
		if divisions != u || clock != u+v || order != firstOrder {
			return fmt.Errorf("wrong rotation counts or terminal phase")
		}
		if workspace.current.Cmp(&workspace.expected) != 0 {
			return fmt.Errorf("wrong phase translation")
		}
	}
	return nil
}

// CheckChunk owns one base and checks ordinary seeds plus every normalized phase.
func CheckChunk(t int, count *int, failure *error) {
	var workspace Workspace
	for v := 2; v <= MaxPhaseCount; v++ {
		for u := 1; u < v; u++ {
			if Gcd(u, v) != 1 {
				continue
			}
			for a := u + v; a <= u+v+2; a++ {
				for s := -8; s <= 8; s++ {
					if s%t == 0 {
						continue
					}
					if err := Configure(&workspace, t, u, v, a, s); err != nil {
						*failure = err
						return
					}
					for seed := int64(-128); seed <= 128; seed++ {
						if seed == 0 {
							continue
						}
						workspace.seed.SetInt64(seed)
						if err := CheckSeed(&workspace, &workspace.seed, u, v); err != nil {
							*failure = fmt.Errorf("t=%d u=%d v=%d a=%d s=%d: %w",
								t, u, v, a, s, err)
							return
						}
						*count++
					}
					for k := 0; k < v; k++ {
						for w := -8; w <= 8; w++ {
							if w%t == 0 {
								continue
							}
							workspace.factor.SetInt64(int64(w))
							workspace.seed.Mul(&workspace.phase[k], &workspace.factor)
							if err := CheckSeed(&workspace, &workspace.seed, u, v); err != nil {
								*failure = fmt.Errorf("t=%d phase=%d: %w", t, k, err)
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

// CheckThresholdBoundary verifies a periodic control one level below the threshold.
func CheckThresholdBoundary() error {
	var workspace Workspace
	workspace.q.SetInt64(2)
	workspace.c.SetInt64(4)
	workspace.d.SetInt64(4)
	workspace.current.SetInt64(1)
	expected := [...]int64{6, 16, 4, 1}
	for _, endpoint := range expected {
		workspace.quotient.QuoRem(&workspace.current, &workspace.d, &workspace.remainder)
		if workspace.remainder.Sign() == 0 {
			workspace.current.Set(&workspace.quotient)
		} else {
			ApplyAffine(&workspace)
		}
		workspace.expected.SetInt64(endpoint)
		if workspace.current.Cmp(&workspace.expected) != 0 {
			return fmt.Errorf("wrong threshold boundary control")
		}
	}
	return nil
}

// main checks bounded certificates, a multiword offset, and the sharp boundary control.
func main() {
	var counts [8]int
	var failures [8]error
	var wait sync.WaitGroup
	for i := range counts {
		wait.Add(1)
		go func(i int) {
			defer wait.Done()
			CheckChunk(i+2, &counts[i], &failures[i])
		}(i)
	}
	wait.Wait()
	total := 0
	for i, count := range counts {
		if failures[i] != nil {
			panic(failures[i])
		}
		total += count
	}
	if total != 2186784 {
		panic(fmt.Errorf("case count %d, expected 2186784", total))
	}
	var workspace Workspace
	for _, s := range [...]int{3, -3} {
		if err := Configure(&workspace, 2, 1, 3, 204, s); err != nil {
			panic(err)
		}
		workspace.seed.SetInt64(12)
		if err := CheckSeed(&workspace, &workspace.seed, 1, 3); err != nil {
			panic(err)
		}
	}
	// Opposite initial signs require alignment before the magnitude bound applies.
	if err := Configure(&workspace, 2, 1, 2, 3, 1); err != nil {
		panic(err)
	}
	workspace.seed.SetInt64(-5)
	if err := CheckSeed(&workspace, &workspace.seed, 1, 2); err != nil {
		panic(err)
	}
	if err := CheckThresholdBoundary(); err != nil {
		panic(err)
	}
	fmt.Printf("verified %d signed two-rotation certificates, two multiword offsets, "+
		"sign-alignment control, and boundary cycle 1,6,16,4; "+
		"no finite-to-infinite inference\n", total)
}
