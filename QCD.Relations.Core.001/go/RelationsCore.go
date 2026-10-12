// SPDX-License-Identifier: CC-BY-4.0
package main

import (
	"fmt"
	"os"
	"sync"
)

// rawGuard bounds every intermediate plain-map state so that no machine word can wrap during a
// sweep: below the guard and with a multiplier of at most sixty-three, the affine branch stays
// below 2^64, so the guard reports failure instead of comparing wrapped values. The sweeps of this
// program use multipliers of at most twenty-three (d at most twenty-four); the test helper reaches
// multiplier fifty-nine (d sixty).
const rawGuard = uint64(1) << 58

// CoreStep applies one instruction of the offset map with multiplier d - 1. The program assumes
// d >= 1; at d = 0 every function here divides by zero and panics.
func CoreStep(d, c, n uint64) uint64 {
	if n%d == 0 {
		return n / d
	}
	return (d-1)*n + c
}

// CoreInDomain reports whether one instruction divides by d, that is, whether n is a multiple
// of d or congruent to c modulo d.
func CoreInDomain(d, c, n uint64) bool {
	return n%d == 0 || n%d == c%d
}

// CoreReturnState returns the state reached after the pending division by d.
func CoreReturnState(d, c, n uint64) uint64 {
	if n%d == 0 {
		return n / d
	}
	return ((d-1)*n + c) / d
}

// CoreReturnSteps returns the number of instructions that realize one return step: one at a
// multiple of d, two at a residue-c state.
func CoreReturnSteps(d, c, n uint64) int {
	if n%d == 0 {
		return 1
	}
	return 2
}

// CoreReturnIterate applies the return map k times.
func CoreReturnIterate(d, c, n uint64, k int) uint64 {
	state := n
	for i := 0; i < k; i++ {
		state = CoreReturnState(d, c, state)
	}
	return state
}

// ReturnRealized reports whether the pending division is realized by its minimal instruction
// count, comparing the plain instruction iterates with the return state.
func ReturnRealized(d, c, n uint64) bool {
	steps := CoreReturnSteps(d, c, n)
	state := n
	for i := 0; i < steps; i++ {
		if state > rawGuard {
			return false
		}
		state = CoreStep(d, c, state)
	}
	return state == CoreReturnState(d, c, n)
}

// ResiduePreserved reports whether one affine step lands on a multiple of d exactly at the
// residue-c start and stays outside the domain at every other non-multiple. A residue-c state is
// congruent to minus itself modulo d, while a generic non-multiple keeps a residue class that is
// neither zero nor c.
func ResiduePreserved(d, c, n uint64) bool {
	if n%d == 0 {
		return CoreStep(d, c, n) == n/d
	}
	next := CoreStep(d, c, n)
	if n%d == c%d {
		return next%d == 0
	}
	return next%d != 0 && next%d != c%d
}

// DescentHolds reports whether a return step strictly decreases a state above the core.
func DescentHolds(d, c, n uint64) bool {
	return CoreReturnState(d, c, n) < n
}

// CoreInvariant reports whether a return step keeps a positive core state inside the core.
func CoreInvariant(d, c, n uint64) bool {
	next := CoreReturnState(d, c, n)
	return 1 <= next && next <= c
}

// ReachesCore reports whether the return orbit of n enters the core within the budget and
// returns the number of return steps needed. For an in-domain positive seed the first hitting
// time is at most n, so the budget only bounds the search.
func ReachesCore(d, c, n uint64, budget int) (int, bool) {
	state := n
	for i := 0; i < budget; i++ {
		if state <= c {
			return i, true
		}
		state = CoreReturnState(d, c, state)
	}
	return budget, state <= c
}

// DomainClosedPrefix reports whether the first p return iterates of x all lie in the domain, so
// that the return step is realized by the plain map at every step of the prefix.
func DomainClosedPrefix(d, c, x uint64, p int) bool {
	state := x
	for k := 0; k < p; k++ {
		if !CoreInDomain(d, c, state) {
			return false
		}
		state = CoreReturnState(d, c, state)
	}
	return true
}

// FirstOutsideDomain returns the first return iterate of x outside the domain together with its
// index, or the prefix length when no such iterate occurs.
func FirstOutsideDomain(d, c, x uint64, limit int) (uint64, int) {
	state := x
	for k := 0; k < limit; k++ {
		if !CoreInDomain(d, c, state) {
			return state, k
		}
		state = CoreReturnState(d, c, state)
	}
	return state, limit
}

// RawRealization mirrors the expansion theorem: for a domain-closed prefix of length p it returns
// the first length j in p..2p with CoreStep iterated j times equal to the p-th return iterate, or
// zero and false when no such length occurs or an intermediate state leaves the guarded range.
func RawRealization(d, c, x uint64, p int) (int, bool) {
	want := CoreReturnIterate(d, c, x, p)
	state := x
	for j := 1; j <= 2*p; j++ {
		state = CoreStep(d, c, state)
		if state > rawGuard {
			return 0, false
		}
		if j >= p && state == want {
			return j, true
		}
	}
	return 0, false
}

// Workspace owns the reusable orbit buffer of one worker and is not goroutine safe.
type Workspace struct {
	orbit []uint64
}

// NewWorkspace allocates an orbit buffer with the given capacity.
func NewWorkspace(capacity int) *Workspace {
	return &Workspace{orbit: make([]uint64, 0, capacity)}
}

// CoreOrbit fills the workspace buffer with the first horizon states of the return orbit of a
// seed and returns that buffer view. The view is invalidated by the next call.
func (w *Workspace) CoreOrbit(d, c, seed uint64, horizon int) []uint64 {
	w.orbit = w.orbit[:0]
	state := seed
	for i := 0; i < horizon; i++ {
		w.orbit = append(w.orbit, state)
		state = CoreReturnState(d, c, state)
	}
	return w.orbit
}

// CorePeriod returns the first repeat delay and the period of a return orbit, or false when no
// repeat occurs within the buffer. The period is verified forward through the whole buffer.
func (w *Workspace) CorePeriod(d, c, seed uint64, horizon int) (int, int, bool) {
	states := w.CoreOrbit(d, c, seed, horizon)
	states = states[:len(states)]
	for i := 0; i < len(states); i++ {
		for j := i + 1; j < len(states); j++ {
			if states[i] != states[j] {
				continue
			}
			period := j - i
			verified := true
			for k := i; k+period < len(states); k++ {
				if states[k] != states[k+period] {
					verified = false
					break
				}
			}
			return i, period, verified
		}
	}
	return 0, 0, false
}

// TrapGrowth reports whether a state outside the domain stays outside it and grows by at least
// one per instruction for the next horizon steps. A walk that would leave the guarded range
// reports failure instead of comparing wrapped values.
func TrapGrowth(d, c, n uint64, horizon int) bool {
	if CoreInDomain(d, c, n) {
		return false
	}
	state := n
	for i := 0; i < horizon; i++ {
		state = CoreStep(d, c, state)
		if state > rawGuard || CoreInDomain(d, c, state) || state < n+uint64(i+1) {
			return false
		}
	}
	return true
}

// CornerChecks reports whether the corner family c = d + 1 satisfies every value, trap and
// uniqueness claim on the bounded range of states from one to d + 1.
func CornerChecks(d uint64) bool {
	c := d + 1
	if CoreReturnState(d, c, 1) != 2 {
		return false
	}
	if CoreReturnState(d, c, d) != 1 {
		return false
	}
	if CoreReturnState(d, c, d+1) != d+1 {
		return false
	}
	if CoreStep(d, c, d+1) != d*(d+1) || CoreStep(d, c, d*(d+1)) != d+1 {
		return false
	}
	fixed := uint64(0)
	for x := uint64(1); x <= c; x++ {
		if x >= 2 && x < d {
			if CoreInDomain(d, c, x) {
				return false
			}
			continue
		}
		if CoreInDomain(d, c, x) && CoreReturnState(d, c, x) == x {
			fixed++
		}
	}
	return fixed == 1
}

// ControlChecks verifies the negative controls recorded for the family: the corner cycle already
// exists at d = 2 next to a second raw cycle, and a state outside the domain grows under every
// instruction.
func ControlChecks() bool {
	if CoreStep(2, 3, 3) != 6 || CoreStep(2, 3, 6) != 3 {
		return false
	}
	second := [...]uint64{1, 4, 2, 1}
	state := second[0]
	for _, want := range second[1:] {
		state = CoreStep(2, 3, state)
		if state != want {
			return false
		}
	}
	if !CornerChecks(2) {
		return false
	}
	return TrapGrowth(5, 2, 1, 6)
}

// Cache records parameter pairs whose sweeps were already run, so that a chunked sweep reports
// each pair once without repeating the work. A pair is marked before its work is done: the flag is
// a memo against duplicated work, not a certificate, and the caller must report the outcome after
// the sweep. It is safe for concurrent use.
type Cache struct {
	mu       sync.Mutex
	verified map[[2]uint64]bool
}

// NewCache returns an empty verification cache.
func NewCache() *Cache {
	return &Cache{verified: make(map[[2]uint64]bool)}
}

// Mark records that the pair was scheduled, before its checks run.
func (c *Cache) Mark(d, w uint64) {
	c.mu.Lock()
	defer c.mu.Unlock()
	c.verified[[2]uint64{d, w}] = true
}

// Seen reports whether the pair was verified before.
func (c *Cache) Seen(d, w uint64) bool {
	c.mu.Lock()
	defer c.mu.Unlock()
	return c.verified[[2]uint64{d, w}]
}

// sweepDomainChecks tests the domain characterisation, the return realisation, descent and core
// invariance for small parameters.
func sweepDomainChecks(checks, failures *uint64) {
	for d := uint64(2); d <= 8; d++ {
		for c := uint64(1); c <= 10; c++ {
			for n := uint64(0); n <= 600; n++ {
				*checks++
				if !ResiduePreserved(d, c, n) {
					*failures++
					fmt.Printf("residue failure: d=%d c=%d n=%d\n", d, c, n)
				}
				if !CoreInDomain(d, c, n) {
					continue
				}
				*checks++
				if !ReturnRealized(d, c, n) {
					*failures++
					fmt.Printf("return failure: d=%d c=%d n=%d\n", d, c, n)
				}
				if n > c {
					*checks++
					if !DescentHolds(d, c, n) {
						*failures++
						fmt.Printf("descent failure: d=%d c=%d n=%d\n", d, c, n)
					}
				}
				if 1 <= n && n <= c {
					*checks++
					if !CoreInvariant(d, c, n) {
						*failures++
						fmt.Printf("core failure: d=%d c=%d n=%d\n", d, c, n)
					}
				}
			}
		}
	}
}

// sweepCoreChecks tests core reachability, periodicity in the core and trap growth.
func sweepCoreChecks(checks, failures *uint64, w *Workspace) {
	for d := uint64(2); d <= 8; d++ {
		for c := uint64(1); c <= 10; c++ {
			for n := uint64(1); n <= 600; n++ {
				if !CoreInDomain(d, c, n) {
					*checks++
					if !TrapGrowth(d, c, n, 12) {
						*failures++
						fmt.Printf("trap failure: d=%d c=%d n=%d\n", d, c, n)
					}
					continue
				}
				steps, reached := ReachesCore(d, c, n, 1024)
				*checks++
				if !reached {
					*failures++
					fmt.Printf("core reach failure: d=%d c=%d n=%d\n", d, c, n)
					continue
				}
				if steps > int(n) {
					*failures++
					fmt.Printf("core reach bound failure: d=%d c=%d n=%d steps=%d\n", d, c, n, steps)
				}
				core := CoreReturnIterate(d, c, n, steps)
				if core < 1 || core > c {
					*failures++
					fmt.Printf("core range failure: d=%d c=%d n=%d core=%d\n", d, c, n, core)
					continue
				}
				_, period, ok := w.CorePeriod(d, c, core, int(c)+2)
				*checks++
				if !ok || period == 0 {
					*failures++
					fmt.Printf("period failure: d=%d c=%d n=%d\n", d, c, n)
				}
			}
		}
	}
}

// sweepCornerChecks tests the corner family, its traps and the raw cycle for every d from three
// up, and the control checks once.
func sweepCornerChecks(checks, failures *uint64) {
	for d := uint64(3); d <= 40; d++ {
		c := d + 1
		*checks++
		if !CornerChecks(d) {
			*failures++
			fmt.Printf("corner failure: d=%d\n", d)
		}
		for x := uint64(2); x < d; x++ {
			*checks++
			if CoreInDomain(d, c, x) {
				*failures++
				fmt.Printf("corner trap failure: d=%d x=%d\n", d, x)
			}
		}
	}
	*checks++
	if !ControlChecks() {
		*failures++
		fmt.Println("control failure")
	}
}

// sweepExpansionChecks verifies the raw realization of every periodic core orbit whose return
// prefix stays in the domain, and the divergence of the first return iterate outside it
// otherwise.
func sweepExpansionChecks(checks, failures *uint64, w *Workspace) {
	for d := uint64(2); d <= 10; d++ {
		for c := uint64(1); c <= 12; c++ {
			for x := uint64(1); x <= c; x++ {
				if !CoreInDomain(d, c, x) {
					continue
				}
				delay, period, ok := w.CorePeriod(d, c, x, int(c)+2)
				if !ok || period == 0 {
					*failures++
					fmt.Printf("core period failure: d=%d c=%d x=%d\n", d, c, x)
					continue
				}
				start := CoreReturnIterate(d, c, x, delay)
				if _, cycle, cycleOK := w.CorePeriod(d, c, start, int(c)+2); !cycleOK || cycle == 0 {
					*failures++
					fmt.Printf("cycle period failure: d=%d c=%d x=%d\n", d, c, x)
					continue
				} else {
					period = cycle
				}
				if DomainClosedPrefix(d, c, start, period) {
					*checks++
					if _, ok := RawRealization(d, c, start, period); !ok {
						*failures++
						fmt.Printf("raw realization failure: d=%d c=%d x=%d p=%d\n", d, c, x, period)
					}
					continue
				}
				trap, _ := FirstOutsideDomain(d, c, start, period)
				*checks++
				if !TrapGrowth(d, c, trap, 8) {
					*failures++
					fmt.Printf("trap divergence failure: d=%d c=%d x=%d n=%d\n", d, c, x, trap)
				}
			}
		}
	}
}

// CoreIterate applies the plain instruction map k times and reports whether every intermediate
// state stayed inside the guarded range.
func CoreIterate(d, c, n uint64, k int) (uint64, bool) {
	state := n
	for i := 0; i < k; i++ {
		state = CoreStep(d, c, state)
		if state > rawGuard {
			return state, false
		}
	}
	return state, true
}

// Classify runs the corner return orbit of a seed and reports one when the orbit reaches the two
// cycle, two when it first leaves the domain, and zero when the budget runs out.
func Classify(d, seed uint64, budget int) int {
	c := d + 1
	state := seed
	for i := 0; i < budget; i++ {
		if state == c || state == d*c {
			return 1
		}
		if !CoreInDomain(d, c, state) {
			return 2
		}
		state = CoreReturnState(d, c, state)
	}
	return 0
}

// CycleBasinCount counts the positive seeds below limit whose corner orbit reaches the two cycle
// within the budget. A seed whose budget expires counts as not reaching, and the caller reports
// that case separately.
func CycleBasinCount(d, limit uint64, budget int) uint64 {
	var count uint64
	for seed := uint64(1); seed < limit; seed++ {
		if Classify(d, seed, budget) == 1 {
			count++
		}
	}
	return count
}

// sweepCornerClassificationChecks verifies that every bounded positive seed either reaches the
// corner two-cycle or leaves the domain and then grows without bound.
func sweepCornerClassificationChecks(checks, failures *uint64) {
	for d := uint64(3); d <= 24; d++ {
		c := d + 1
		for seed := uint64(1); seed <= 500; seed++ {
			*checks++
			switch Classify(d, seed, 4096) {
			case 1:
				continue
			case 2:
				state := seed
				for state%d == 0 || state%d == c%d {
					state = CoreReturnState(d, c, state)
				}
				if !TrapGrowth(d, c, state, 8) {
					*failures++
					fmt.Printf("classification growth failure: d=%d seed=%d\n", d, seed)
				}
			default:
				*failures++
				fmt.Printf("classification failure: d=%d seed=%d\n", d, seed)
			}
		}
	}
}

// sweepPeriodicPointChecks verifies the periodic-point classification: at positive lengths only the
// two cycle states are fixed by the k-th corner iterate, and only at even lengths.
func sweepPeriodicPointChecks(checks, failures *uint64) {
	for d := uint64(3); d <= 12; d++ {
		c := d + 1
		for k := 1; k <= 8; k++ {
			even := k%2 == 0
			for x := uint64(1); x <= 200; x++ {
				*checks++
				state, ok := CoreIterate(d, c, x, k)
				fixed := ok && state == x
				onCycle := x == c || x == d*c
				if fixed != (onCycle && even) {
					*failures++
					fmt.Printf("periodic point failure: d=%d k=%d x=%d\n", d, k, x)
				}
			}
		}
	}
}

// parallelCoreSweep partitions a parameter range over independent workers and returns the check
// and failure totals of the chunked sweep.
func parallelCoreSweep(chunks int, cache *Cache) (uint64, uint64) {
	var checks, failures uint64
	var mu sync.Mutex
	var group sync.WaitGroup
	for chunk := 0; chunk < chunks; chunk++ {
		group.Add(1)
		go func(chunk int) {
			defer group.Done()
			w := NewWorkspace(64)
			var localChecks, localFailures uint64
			lo := uint64(chunk)*4 + 2
			hi := lo + 3
			for d := lo; d <= hi; d++ {
				for c := uint64(1); c <= 8; c++ {
					if cache.Seen(d, c) {
						continue
					}
					cache.Mark(d, c)
					horizon := int(c) + 2
					for n := uint64(1); n <= 200; n++ {
						if !CoreInDomain(d, c, n) {
							continue
						}
						localChecks++
						if !ReturnRealized(d, c, n) {
							localFailures++
						}
						if n > c {
							localChecks++
							if !DescentHolds(d, c, n) {
								localFailures++
							}
						}
						core := CoreReturnIterate(d, c, n, 1024)
						localChecks++
						if _, period, ok := w.CorePeriod(d, c, core, horizon); !ok || period == 0 {
							localFailures++
						}
					}
				}
			}
			mu.Lock()
			checks += localChecks
			failures += localFailures
			mu.Unlock()
		}(chunk)
	}
	group.Wait()
	return checks, failures
}

// main runs the bounded certificate sweep and reports the totals; any failure exits nonzero.
func main() {
	var checks, failures uint64
	w := NewWorkspace(64)
	sweepDomainChecks(&checks, &failures)
	sweepCoreChecks(&checks, &failures, w)
	sweepCornerChecks(&checks, &failures)
	sweepCornerClassificationChecks(&checks, &failures)
	sweepPeriodicPointChecks(&checks, &failures)
	sweepExpansionChecks(&checks, &failures, w)
	parallelChecks, parallelFailures := parallelCoreSweep(4, NewCache())
	checks += parallelChecks
	failures += parallelFailures
	fmt.Printf("relation core checks: %d, failures: %d\n", checks, failures)
	if failures != 0 {
		os.Exit(1)
	}
}
