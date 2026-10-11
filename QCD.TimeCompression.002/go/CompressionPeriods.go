// SPDX-License-Identifier: CC-BY-4.0
// This bounded check compares primitive compressed cycles with their complete raw expansions.
package main

import (
	"fmt"
	"math/big"
	"os"
	"sync"
)

const SampleBudget = 32

// Workspace owns the reusable arithmetic and orbit buffers for one independent chunk.
type Workspace struct {
	states    [SampleBudget + 1]big.Int
	current   big.Int
	next      big.Int
	remainder big.Int
	q         big.Int
	c         big.Int
	Q         big.Int
	C         big.Int
	d         big.Int
}

// InitializeWorkspace reserves more limbs than the stated finite parameter range needs.
func InitializeWorkspace(workspace *Workspace) {
	var one big.Int
	one.SetInt64(1)
	buffers := make([]*big.Int, 0, len(workspace.states)+8)
	buffers = append(buffers,
		&workspace.current, &workspace.next, &workspace.remainder,
		&workspace.q, &workspace.c, &workspace.Q, &workspace.C, &workspace.d,
	)
	for i := range workspace.states {
		buffers = append(buffers, &workspace.states[i])
	}
	for _, buffer := range buffers {
		buffer.Lsh(&one, 256)
		buffer.SetInt64(0)
	}
}

// ApplyRawStep uses exact signed division only on the divisible branch.
func ApplyRawStep(workspace *Workspace, q, c, in, out *big.Int) bool {
	out.QuoRem(in, &workspace.d, &workspace.remainder)
	if workspace.remainder.Sign() == 0 {
		return false
	}
	out.Mul(q, in)
	out.Add(out, c)
	return true
}

// CheckExpandedPeriod rejects invalid indices and every shorter positive raw return.
func CheckExpandedPeriod(workspace *Workspace, first, last, a int) error {
	if first < 0 || first >= last || last > SampleBudget || a < 0 || a > 3 {
		return fmt.Errorf("invalid bounded period indices or exponent: %d %d %d", first, last, a)
	}
	period := last - first
	affines := 0
	for i := first; i < last; i++ {
		workspace.current.QuoRem(&workspace.states[i], &workspace.d, &workspace.remainder)
		if workspace.remainder.Sign() != 0 {
			affines++
		}
	}
	expanded := period + a*affines
	seed := &workspace.states[first]
	workspace.current.Set(seed)
	for time := 1; time <= expanded; time++ {
		ApplyRawStep(workspace, &workspace.Q, &workspace.C,
			&workspace.current, &workspace.next)
		workspace.current.Set(&workspace.next)
		if workspace.current.Cmp(seed) == 0 && time != expanded {
			return fmt.Errorf("shorter raw return: time=%d expanded=%d", time, expanded)
		}
	}
	if workspace.current.Cmp(seed) != 0 {
		return fmt.Errorf("expanded endpoint mismatch: period=%d affines=%d", period, affines)
	}
	return nil
}

// CheckSeed searches only the stated sample budget; absence of a repeat resolves nothing.
func CheckSeed(workspace *Workspace, seed int64, a int) (bool, error) {
	workspace.states[0].SetInt64(seed)
	for last := 1; last <= SampleBudget; last++ {
		ApplyRawStep(workspace, &workspace.q, &workspace.c,
			&workspace.states[last-1], &workspace.states[last])
		for first := 0; first < last; first++ {
			if workspace.states[first].Cmp(&workspace.states[last]) == 0 {
				return true, CheckExpandedPeriod(workspace, first, last, a)
			}
		}
	}
	return false, nil
}

// CheckPeriodRange reuses one initialized workspace across its finite parameter grid.
func CheckPeriodRange(workspace *Workspace, first, last int, cases, cycles *int) error {
	divisors := [...]int64{-5, -4, -3, -2, 2, 3, 4, 5}
	for _, d := range divisors {
		workspace.d.SetInt64(d)
		for a := 0; a <= 3; a++ {
			power := int64(1)
			for i := 0; i < a; i++ {
				power *= d
			}
			for q := int64(-3); q <= 3; q++ {
				for c := int64(-3); c <= 3; c++ {
					workspace.q.SetInt64(q)
					workspace.c.SetInt64(c)
					workspace.Q.SetInt64(power * q)
					workspace.C.SetInt64(power * c)
					for seed := first; seed < last; seed++ {
						found, err := CheckSeed(workspace, int64(seed), a)
						(*cases)++
						if err != nil {
							return fmt.Errorf("d=%d a=%d q=%d c=%d seed=%d: %w",
								d, a, q, c, seed, err)
						}
						if found {
							(*cycles)++
						}
					}
				}
			}
		}
	}
	return nil
}

// CheckPeriodChunk owns its workspace and nonnil output slots over a half-open seed chunk.
func CheckPeriodChunk(first, last int, cases, cycles *int, failure *error) {
	workspace := new(Workspace)
	InitializeWorkspace(workspace)
	*failure = CheckPeriodRange(workspace, first, last, cases, cycles)
}

// main reports finite coverage separately from the mathematically proved universal transfer.
func main() {
	const chunks = 8
	var cases, cycles [chunks]int
	var failures [chunks]error
	var group sync.WaitGroup
	for chunk := 0; chunk < chunks; chunk++ {
		first := -30 + 61*chunk/chunks
		last := -30 + 61*(chunk+1)/chunks
		group.Add(1)
		go func(chunk, first, last int) {
			defer group.Done()
			CheckPeriodChunk(first, last, &cases[chunk], &cycles[chunk], &failures[chunk])
		}(chunk, first, last)
	}
	group.Wait()
	caseTotal, cycleTotal := 0, 0
	for chunk := 0; chunk < chunks; chunk++ {
		if failures[chunk] != nil {
			fmt.Fprintln(os.Stderr, failures[chunk])
			os.Exit(1)
		}
		caseTotal += cases[chunk]
		cycleTotal += cycles[chunk]
	}
	fmt.Printf("checked %d finite seeds, %d primitive-cycle expansion certificates; "+
		"no-repeat-by-%d cases remain undecided\n", caseTotal, cycleTotal, SampleBudget)
}
