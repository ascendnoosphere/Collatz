// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"fmt"
	"math/big"
	"sync"
)

// Computational limits bound this replay, not the universal Lean statements.
const (
	MaxBinaryExponent  = 64
	MaxTernaryExponent = 32
	MaxSeedBits        = 512
	StorageBits        = 2048
	EntryStepLimit     = 4096
	TailRawSteps       = 32
	ClassicalSteps     = 16
)

// Workspace owns every operand and intermediate used by one sequential seed chunk.
type Workspace struct {
	a, b               int
	configured         bool
	q, c, scale, unitC big.Int
	one, two, three    big.Int
	raw, compressed    big.Int
	unit, classical    big.Int
	next, remainder    big.Int
	expected, quotient big.Int
	storage            [16]big.Int
}

// Reserve retains a cold-allocated backing array when its active integer becomes small.
func Reserve(value, storage *big.Int) {
	storage.SetBit(storage, StorageBits-1, 1)
	value.Set(storage)
	value.SetInt64(0)
}

// Configure refuses invalid resources before mutation and reserves disjoint hot operands.
func Configure(workspace *Workspace, a, b int) error {
	if workspace == nil || a < 0 || a > MaxBinaryExponent ||
		b < 0 || b > MaxTernaryExponent {
		return fmt.Errorf("invalid bounded binary or ternary exponent")
	}
	values := []*big.Int{
		&workspace.q, &workspace.c, &workspace.scale, &workspace.unitC,
		&workspace.one, &workspace.two, &workspace.three,
		&workspace.raw, &workspace.compressed, &workspace.unit, &workspace.classical,
		&workspace.next, &workspace.remainder, &workspace.expected, &workspace.quotient,
	}
	for i, value := range values {
		Reserve(value, &workspace.storage[i])
	}
	workspace.a, workspace.b = a, b
	workspace.one.SetInt64(1)
	workspace.two.SetInt64(2)
	workspace.three.SetInt64(3)
	workspace.unitC.Lsh(&workspace.one, uint(a))
	workspace.q.Mul(&workspace.unitC, &workspace.three)
	workspace.quotient.SetInt64(int64(b))
	workspace.scale.Exp(&workspace.three, &workspace.quotient, nil)
	workspace.c.Mul(&workspace.unitC, &workspace.scale)
	workspace.configured = true
	return nil
}

// Step uses division only on an even state and returns whether an affine branch occurred.
func Step(state, q, c *big.Int, workspace *Workspace) bool {
	if state.Bit(0) == 0 {
		workspace.next.QuoRem(state, &workspace.two, &workspace.remainder)
		state.Set(&workspace.next)
		return false
	}
	workspace.next.Mul(q, state)
	workspace.next.Add(&workspace.next, c)
	state.Set(&workspace.next)
	return true
}

// Entered tests exact lattice membership while preserving the state and normalized quotient.
func Entered(workspace *Workspace) bool {
	workspace.quotient.QuoRem(&workspace.compressed, &workspace.scale, &workspace.remainder)
	return workspace.remainder.Sign() == 0
}

// CheckSeed checks compression, finite entry and two distinct post-entry clock correspondences.
func CheckSeed(workspace *Workspace, seed *big.Int) error {
	if workspace == nil || !workspace.configured || seed == nil ||
		seed.Sign() == 0 || seed.BitLen() > MaxSeedBits {
		return fmt.Errorf("nil, zero, oversized seed or unconfigured workspace")
	}
	workspace.raw.Set(seed)
	workspace.compressed.Set(seed)
	compressedAffines, rawAffines := 0, 0
	steps := 0
	for !Entered(workspace) {
		if steps == EntryStepLimit {
			return fmt.Errorf("entry not observed within the bounded compressed prefix")
		}
		clock := 1
		if workspace.compressed.Bit(0) != 0 {
			clock += workspace.a
			compressedAffines++
		}
		Step(&workspace.compressed, &workspace.three, &workspace.scale, workspace)
		for j := 1; j <= clock; j++ {
			if Step(&workspace.raw, &workspace.q, &workspace.c, workspace) {
				rawAffines++
			}
			if j < clock && workspace.raw.Bit(0) != 0 {
				return fmt.Errorf("a forced-division interior lost its binary factor")
			}
			if j < clock && workspace.raw.Cmp(&workspace.scale) == 0 {
				return fmt.Errorf("an odd singleton target appeared at a block interior")
			}
		}
		if workspace.raw.Cmp(&workspace.compressed) != 0 ||
			rawAffines != compressedAffines || compressedAffines > workspace.b {
			return fmt.Errorf("compressed endpoint or affine entry budget mismatch")
		}
		steps++
	}

	// The entered quotient drives the binary-power map on the SAME future raw clock.
	workspace.unit.Set(&workspace.quotient)
	workspace.classical.Set(&workspace.quotient)
	for j := 0; j < TailRawSteps; j++ {
		rawAffine := Step(&workspace.raw, &workspace.q, &workspace.c, workspace)
		unitAffine := Step(&workspace.unit, &workspace.q, &workspace.unitC, workspace)
		workspace.expected.Mul(&workspace.scale, &workspace.unit)
		if rawAffine != unitAffine || workspace.raw.Cmp(&workspace.expected) != 0 {
			return fmt.Errorf("the invariant-lattice raw tail failed")
		}
	}

	// Reset to the common entry witness; classical steps require variable binary clocks.
	workspace.raw.Set(&workspace.compressed)
	for k := 0; k < ClassicalSteps; k++ {
		clock := 1
		if workspace.classical.Bit(0) != 0 {
			clock += workspace.a
		}
		Step(&workspace.classical, &workspace.three, &workspace.one, workspace)
		for j := 1; j <= clock; j++ {
			Step(&workspace.raw, &workspace.q, &workspace.c, workspace)
			if j < clock && workspace.raw.Bit(0) != 0 {
				return fmt.Errorf("classical expansion contains an illegal interior")
			}
		}
		workspace.expected.Mul(&workspace.scale, &workspace.classical)
		if workspace.raw.Cmp(&workspace.expected) != 0 ||
			(workspace.raw.Cmp(&workspace.scale) == 0) !=
				(workspace.classical.Cmp(&workspace.one) == 0) {
			return fmt.Errorf("classical endpoint or exact singleton target mismatch")
		}
	}
	return nil
}

// CheckCycle replays every raw phase and rejects any shorter return to the odd designated seed.
func CheckCycle(workspace *Workspace) error {
	if workspace == nil || !workspace.configured {
		return fmt.Errorf("unconfigured cycle workspace")
	}
	workspace.raw.Set(&workspace.scale)
	for r := 1; r <= workspace.a+3; r++ {
		affine := Step(&workspace.raw, &workspace.q, &workspace.c, workspace)
		if affine != (r == 1) {
			return fmt.Errorf("designated cycle has an unexpected branch")
		}
		if r < workspace.a+3 {
			workspace.expected.Lsh(&workspace.scale, uint(workspace.a+3-r))
		} else {
			workspace.expected.Set(&workspace.scale)
		}
		if workspace.raw.Cmp(&workspace.expected) != 0 ||
			(workspace.raw.Cmp(&workspace.scale) == 0) != (r == workspace.a+3) {
			return fmt.Errorf("designated raw phase or primitive period mismatch")
		}
	}
	return nil
}

// CheckChunk assigns each binary exponent to exactly one owner and counts finite certificates.
func CheckChunk(chunk int, result *uint64, failure *error) {
	workspace := &Workspace{}
	var seed, seedStorage big.Int
	Reserve(&seed, &seedStorage)
	for a := chunk; a <= 16; a += 8 {
		for b := 0; b <= 12; b++ {
			if err := Configure(workspace, a, b); err != nil {
				*failure = err
				return
			}
			if err := CheckCycle(workspace); err != nil {
				*failure = err
				return
			}
			for n := int64(-64); n <= 64; n++ {
				if n == 0 {
					continue
				}
				seed.SetInt64(n)
				if err := CheckSeed(workspace, &seed); err != nil {
					*failure = fmt.Errorf("a=%d b=%d seed=%d: %w", a, b, n, err)
					return
				}
				*result++
			}
		}
	}
}

// main joins eight owned chunks; a bounded prefix or certificate is never a convergence proof.
func main() {
	var results [8]uint64
	var failures [8]error
	var wait sync.WaitGroup
	for chunk := 0; chunk < len(results); chunk++ {
		wait.Add(1)
		go func(chunk int) {
			defer wait.Done()
			CheckChunk(chunk, &results[chunk], &failures[chunk])
		}(chunk)
	}
	wait.Wait()
	var total uint64
	for chunk, count := range results {
		if failures[chunk] != nil {
			panic(failures[chunk])
		}
		total += count
	}
	fmt.Printf("checked %d bounded clock, entry and tail certificates\n", total)
}
