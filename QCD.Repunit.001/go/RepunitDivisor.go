// SPDX-License-Identifier: CC-BY-4.0
//
// Exact certificate for QCD.Repunit.001. The program checks the repunit
// divisor identities, the exact multiplicative order, the unit cycle of the
// seed 1, the residue walk from 0, the trap set and the return map over a
// bounded grid, and reports the number of checks and the number of failures.

package main

import (
	"fmt"
	"math/big"
	"os"
	"sync"
)

const (
	repunitMaxQ    = 20 // multiplier bound of the sweeps
	repunitMaxK    = 20 // divisor-index bound of the sweeps
	repunitSeeds   = 200
	repunitSteps   = 24
	repunitWorkers = 4
)

// BigOne is the constant one shared by the sweeps.
var BigOne = big.NewInt(1)

// Totals counts the checks and the failures of one slice.
type Totals struct {
	Checks   uint64
	Failures uint64
}

// Workspace holds the buffers reused by the step and return walks.
type Workspace struct {
	Sum  *big.Int
	Pow  *big.Int
	Cur  *big.Int
	Next *big.Int
	Rem  *big.Int
	Base *big.Int
}

// NewWorkspace returns a workspace with six fresh value buffers.
func NewWorkspace() *Workspace {
	return &Workspace{
		Sum:  new(big.Int),
		Pow:  new(big.Int),
		Cur:  new(big.Int),
		Next: new(big.Int),
		Rem:  new(big.Int),
		Base: new(big.Int),
	}
}

// RepunitSum returns 1 + q + ... + q^(k-1) as a fresh value.
func RepunitSum(q uint64, k int) *big.Int {
	sum := new(big.Int)
	pow := big.NewInt(1)
	base := new(big.Int).SetUint64(q)
	for j := 0; j < k; j++ {
		sum.Add(sum, pow)
		pow.Mul(pow, base)
	}
	return sum
}

// StepBig applies one instruction with divisor D and unit offset at the state
// n, writing the result into out; out must be distinct from n and from D.
func (w *Workspace) StepBig(q uint64, D, n, out *big.Int) *big.Int {
	out.QuoRem(n, D, w.Rem)
	if w.Rem.Sign() == 0 {
		return out
	}
	out.Mul(w.Base.SetUint64(q), n)
	return out.Add(out, BigOne)
}

// check records one failure when the condition fails.
func (t *Totals) check(ok bool) {
	t.Checks++
	if !ok {
		t.Failures++
	}
}

// sweepDivisors checks the divisor identity (q-1) S_k = q^k - 1 and the
// divisibility S_k | q^k - 1 for every multiplier and index of the grid.
func sweepDivisors(q uint64, _ *Workspace, t *Totals) {
	base := new(big.Int).SetUint64(q - 1)
	for k := 1; k <= repunitMaxK; k++ {
		sum := RepunitSum(q, k)
		pow := new(big.Int).Exp(big.NewInt(int64(q)), big.NewInt(int64(k)), nil)
		pow.Sub(pow, BigOne)
		lhs := new(big.Int).Mul(base, sum)
		t.check(lhs.Cmp(pow) == 0)
		t.check(new(big.Int).Mod(pow, sum).Sign() == 0)
	}
}

// sweepOrder checks that the order of q modulo S_k is exactly k: q^k = 1 and
// q^j is not 1 for 0 < j < k.
func sweepOrder(q uint64, _ *Workspace, t *Totals) {
	for k := 2; k <= repunitMaxK; k++ {
		sum := RepunitSum(q, k)
		pow := new(big.Int).Exp(big.NewInt(int64(q)), big.NewInt(int64(k)), sum)
		t.check(pow.Cmp(BigOne) == 0)
		for j := 1; j < k; j++ {
			pow = new(big.Int).Exp(big.NewInt(int64(q)), big.NewInt(int64(j)), sum)
			t.check(pow.Cmp(BigOne) != 0)
		}
	}
}

// sweepCycle checks the orbit of the seed 1 with divisor S_k: the state after
// j steps is S_(j+1) for j < k and 1 at j = k, and no earlier state is 1.
func sweepCycle(q uint64, w *Workspace, t *Totals) {
	for k := 2; k <= repunitMaxK; k++ {
		sum := RepunitSum(q, k)
		w.Cur.SetUint64(1)
		states := make([]*big.Int, 0, k)
		for j := 1; j <= k; j++ {
			w.StepBig(q, sum, w.Cur, w.Next)
			w.Cur, w.Next = w.Next, w.Cur
			states = append(states, new(big.Int).Set(w.Cur))
		}
		for j := 0; j < k; j++ {
			want := RepunitSum(q, j+2)
			if j == k-1 {
				want = BigOne
			}
			t.check(states[j].Cmp(want) == 0)
			if j < k-1 {
				t.check(states[j].Cmp(BigOne) != 0)
			}
		}
	}
}

// sweepResidues checks the residue walk from 0 modulo S_k: the state after j
// steps is S_j, the walk returns to 0 after k steps, and the first k residues
// are pairwise distinct.
func sweepResidues(q uint64, w *Workspace, t *Totals) {
	for k := 2; k <= repunitMaxK; k++ {
		sum := RepunitSum(q, k)
		w.Cur.SetUint64(0)
		seen := make(map[string]bool, k)
		for j := 1; j <= k; j++ {
			w.Next.Mul(w.Base.SetUint64(q), w.Cur)
			w.Next.Add(w.Next, BigOne)
			w.Next.Mod(w.Next, sum)
			w.Cur, w.Next = w.Next, w.Cur
			want := RepunitSum(q, j)
			want.Mod(want, sum)
			t.check(w.Cur.Cmp(want) == 0)
			t.check(!seen[w.Cur.String()])
			seen[w.Cur.String()] = true
		}
		for j := k + 1; j <= 2*k; j++ {
			w.Next.Mul(w.Base.SetUint64(q), w.Cur)
			w.Next.Add(w.Next, BigOne)
			w.Next.Mod(w.Next, sum)
			w.Cur, w.Next = w.Next, w.Cur
			want := RepunitSum(q, j)
			want.Mod(want, sum)
			t.check(w.Cur.Cmp(want) == 0)
		}
		// At time 2k the walk is back at the residue 0 of the starting state.
		t.check(w.Cur.Sign() == 0)
	}
}

// sweepTraps checks that zero is the only state sent to zero by one
// instruction with divisor S_k and unit offset.
func sweepTraps(q uint64, w *Workspace, t *Totals) {
	for k := 2; k <= repunitMaxK; k++ {
		sum := RepunitSum(q, k)
		for n := 0; n <= repunitSeeds; n++ {
			w.Cur.SetUint64(uint64(n))
			w.StepBig(q, sum, w.Cur, w.Next)
			t.check((w.Next.Sign() == 0) == (n == 0))
		}
	}
}

// sweepReturns checks that the return map fixes 1: after k-1 affine events the
// state is S_k, and dividing the multiple returns 1.
func sweepReturns(q uint64, w *Workspace, t *Totals) {
	for k := 2; k <= repunitMaxK; k++ {
		w.Cur.SetUint64(1)
		w.Next.SetUint64(1)
		for j := 1; j < k; j++ {
			w.Next.Mul(w.Base.SetUint64(q), w.Cur)
			w.Next.Add(w.Next, BigOne)
			w.Cur, w.Next = w.Next, w.Cur
		}
		sum := RepunitSum(q, k)
		t.check(w.Cur.Cmp(sum) == 0)
		w.Next.Quo(w.Cur, sum)
		t.check(w.Next.Cmp(BigOne) == 0)
	}
}

// sweepControls checks the boundaries of the family. The multiplier one
// controls are discriminating: the repunit sum degenerates to the index, and
// the order claim of the slice fails there because 1^j is one for every
// 0 < j < k, which the recorded witnesses assert. The divisor one makes every
// state fixed, and a divisor that is not a repunit sum gives no return to one
// within the horizon.
func sweepControls(w *Workspace, t *Totals) {
	index := new(big.Int)
	for k := 2; k <= repunitMaxK; k++ {
		sum := RepunitSum(1, k)
		t.check(sum.Cmp(index.SetUint64(uint64(k))) == 0)
		for j := 1; j < k; j++ {
			pow := new(big.Int).Exp(BigOne, big.NewInt(int64(j)), sum)
			t.check(pow.Cmp(BigOne) == 0)
		}
	}
	for q := uint64(2); q <= repunitMaxQ; q++ {
		oneD := big.NewInt(1)
		for n := uint64(0); n <= 10; n++ {
			w.Cur.SetUint64(n)
			w.StepBig(q, oneD, w.Cur, w.Next)
			t.check(w.Next.Cmp(w.Cur) == 0)
		}
	}
	w.Cur.SetUint64(1)
	for j := 0; j < repunitSteps; j++ {
		w.StepBig(2, big.NewInt(5), w.Cur, w.Next)
		w.Cur, w.Next = w.Next, w.Cur
		t.check(w.Cur.Cmp(BigOne) != 0)
	}
}

// runParallel sweeps q = 2..repunitMaxQ in chunks and sums the totals.
func runParallel(fn func(uint64, *Workspace, *Totals)) Totals {
	chunks := make([]Totals, repunitWorkers)
	var wg sync.WaitGroup
	width := uint64(repunitMaxQ-1+repunitWorkers-1) / repunitWorkers
	for i := 0; i < repunitWorkers; i++ {
		lo := 2 + uint64(i)*width
		hi := lo + width - 1
		if hi > repunitMaxQ {
			hi = repunitMaxQ
		}
		if lo > hi {
			continue
		}
		wg.Add(1)
		go func(idx int, lo, hi uint64) {
			defer wg.Done()
			w := NewWorkspace()
			for q := lo; q <= hi; q++ {
				fn(q, w, &chunks[idx])
			}
		}(i, lo, hi)
	}
	wg.Wait()
	var total Totals
	for _, chunk := range chunks {
		total.Checks += chunk.Checks
		total.Failures += chunk.Failures
	}
	return total
}

// main runs every slice, prints the certificate and exits nonzero on failure.
func main() {
	slices := []struct {
		name string
		run  func(uint64, *Workspace, *Totals)
	}{
		{"divisors", sweepDivisors},
		{"order", sweepOrder},
		{"cycle", sweepCycle},
		{"residues", sweepResidues},
		{"traps", sweepTraps},
		{"returns", sweepReturns},
	}
	var total Totals
	for _, slice := range slices {
		got := runParallel(slice.run)
		fmt.Printf("%-9s checks %7d failures %d\n", slice.name, got.Checks, got.Failures)
		total.Checks += got.Checks
		total.Failures += got.Failures
	}
	control := Totals{}
	sweepControls(NewWorkspace(), &control)
	fmt.Printf("%-9s checks %7d failures %d\n", "controls", control.Checks, control.Failures)
	total.Checks += control.Checks
	total.Failures += control.Failures
	fmt.Printf("repunit divisor checks: %d, failures: %d\n", total.Checks, total.Failures)
	if total.Failures != 0 {
		os.Exit(1)
	}
}
