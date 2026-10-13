<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# QCD.Relations.Core.001 — Return cores of the multiplier `d - 1` map

## Statement and domain

Fix integers $d\ge 2$ and $c\ge 1$ and let
$$
\operatorname{CoreMap}_{d,c}(n)=
\begin{cases}
n/d, & d\mid n,\\
(d-1)n+c, & d\nmid n,
\end{cases}
$$
the multiplier $q=d-1$ case of the generalized Collatz map with divisor
$d$. Write $C^{k}$ for $k$ instructions, so $C^{0}$ is the identity and
$C^{k+1}=C\circ C^{k}$. A state is *accessible* when one instruction divides
by $d$, that is, when $d\mid n$ or $n\equiv c\pmod d$, and the state
after that division is the *return map*
$$
\operatorname{CoreReturn}_{d,c}(n)=
\begin{cases}
n/d, & d\mid n,\\
((d-1)n+c)/d, & d\nmid n.
\end{cases}
$$
The return map is defined for every $n$, but its steps are realized by the
original map only at accessible states. All statements are over $\mathbb{N}$;
division is exact where written.

The results below separate five obligations: the residue algebra of one
instruction; the strict contraction of the return map above the core
$\{1,\dots,c\}$ and its invariance on the core; the realization of return
steps by one or two original instructions; the resulting trap-or-core
dichotomy; and the complete classification of the corner case $c=d+1$ with
$d\ge 3$.

## Numbered results

| # | Claim | Lean |
| --- | --- | --- |
| .1 | At a non-multiple of $d$, one affine instruction is divisible by $d$ exactly at the residue-$c$ states, and otherwise keeps a residue class that is neither $0$ nor $c$; at a residue-$c$ state, $(d-1)n+c$ is divisible by $d$. | `CoreMapDivisibleIff`, `CoreMapResidueIff`, `CoreDomainDivisible`, `CoreMapCast` |
| .2 | Branch values: `CoreMap d c n = n / d` at a multiple of `d` and `= (d-1)*n+c` otherwise; the same split for `CoreReturn`. | `CoreMapOfDvd`, `CoreMapOfNotDvd`, `CoreReturnOfDvd`, `CoreReturnOfNotDvd` |
| .3 | Strict contraction: for $d\ge2$ and $c<n$, one return step strictly decreases the state (`CoreReturnDecrease`); a positive multiple of $d$ decreases under one instruction (`CoreMapDivisibleDecrease`), and for $c\ge1$ a positive non-multiple strictly increases under one instruction (`CoreMapFreeIncrease`). | `CoreReturnDecrease`, `CoreMapDivisibleDecrease`, `CoreMapFreeIncrease` |
| .4 | Core invariance: for $d\ge2$, $c\ge1$ and $1\le n\le c$, every return iterate again satisfies $1\le \operatorname{CoreReturn}^{\;k}(n)\le c$. | `CoreReturnCore`, `CoreReturnIterateCore`, `CoreReturnPositive`, `CoreReturnIteratePositive` |
| .5 | Traps: a state outside the domain stays outside the domain forever, grows strictly at every instruction, and exceeds every bound. | `CoreMapNotDomain`, `CoreTrapNotDomain`, `CoreTrapStrictMono`, `CoreTrapGrowth`, `CoreTrapUnbounded` |
| .6 | Realization: one instruction realizes the return step at a multiple of $d$, two instructions realize it at a residue-$c$ state; along a domain-closed prefix of length $p$ some $j$ with $p\le j\le 2p$ realizes the $p$-th return iterate. | `CoreReturnRealizeDvd`, `CoreReturnRealizeMod`, `CoreReturnRealizeModCompose`, `CoreReturnRawRealization` |
| .7 | Cycle expansion: a return cycle of length $p>0$ whose prefix stays in the domain expands to a raw cycle whose length $j$ satisfies $0<j\le 2p$. | `CoreReturnCycleRaw` |
| .8 | Reachability: every positive state reaches the core, within at most its own number of return steps. | `CoreReturnReachesCore`, `CoreReturnReachesCoreBounded` |
| .9 | Periodicity: every positive state has an eventually periodic return orbit inside the core. | `CoreReturnEventuallyPeriodic` |
| .10 | Dichotomy: every positive state either has an iterate outside the domain, after which the raw orbit passes every bound, or has all its iterates inside the domain. | `CoreMapDichotomy` |
| .11 | Corner core $c=d+1$: for $d\ge3$ the positive accessible states up to $d+1$ are exactly $1$, $d$ and $d+1$, and every $2\le x<d$ is inaccessible; for $d\ge2$ the return values at $1$, $d$ and $d+1$ are $2$, $1$ and $d+1$, and $d+1$ is the only accessible fixed point of the return map on $[1,d+1]$. | `CoreCornerModSelf`, `CoreCornerCoreStates`, `CoreCornerCoreStatesIff`, `CoreReturnCornerOne`, `CoreReturnCornerD`, `CoreReturnCornerSelf`, `CoreMapCornerTrap`, `CoreReturnCornerFixedUnique` |
| .12 | Corner cycle: $d+1\mapsto d(d+1)\mapsto d+1$ under the original map; the two states are periodic and every iterate of a cycle state stays on the cycle; even instruction counts fix each cycle state and odd counts exchange them. | `CoreMapCornerCycleSteps`, `CoreMapCornerCycle`, `CoreMapCornerCycleBack`, `CoreCornerCycleIterateEven`, `CoreCornerCycleIterateOdd`, `CoreCornerCycleIterateBack`, `CoreCornerCycleIterateBackOdd`, `CoreCornerCycleInvariant` |
| .13 | Corner classification: every positive state either leaves the domain, after which the orbit passes every bound, or reaches $d+1$ or $d(d+1)$. | `CoreCornerClassification`, `CoreCornerDomainForeverHitsCycle`, `CoreCornerIterateRealized` |
| .14 | Corner periodic points: for positive $k$, $C^{k}(x)=x$ holds exactly for the two cycle states at even $k$. | `CoreCornerPeriodicPointCycle`, `CoreCornerPeriodicIff` |

Claim .14 is the counting content of the periodic-point zeta function: the
number of positive fixed points of $C^{k}$ is $2$ for even $k$ and $0$
for odd $k$, so the zeta function of the single raw cycle of length two is
$1/(1-z^{2})$ on the positive states. The fixed point $0$ is excluded by
the positivity hypothesis, so a count over all nonnegative fixed points would
differ at odd $k$.

## Reduction and recovery

**Original obligation.** For $q=d-1$ and every $c\ge1$: only the
residues $0$ and $c$ are accessible, both first-division branches strictly
decrease above the core, core endpoints are positive and at most $c$, and
therefore every positive orbit either enters a trap and diverges or becomes
periodic in the return core; the finite core graph exhausts periods and
heights, and its cycles expand to raw cycles. For $c=d+1$ and $d\ge3$: the
only accessible core states are $1,d,d+1$, their return values are
$2,1,d+1$, all other core states are trapped, the only positive raw cycle is
$d+1\mapsto d(d+1)\mapsto d+1$, and the integer periodic-point zeta is
$1/(1-z^{2})$.

**Replacement obligations.** Six finite obligations replace the argument, all over $\mathbb{N}$ with explicit hypotheses: (i) the residue
algebra `.1`; (ii) contraction and core invariance `.3`, `.4`; (iii) trap
growth `.5`; (iv) realization and expansion `.6`, `.7`; (v) reachability and
pigeonhole periodicity `.8`, `.9`; (vi) the corner computation `.11`–`.14`.

**Recovery.** The original classification follows from the replacement
obligations: `.10` splits a positive orbit into the trap case, where `.5`
supplies strict growth and unboundedness, and the domain-closed case, where
`.6` exhibits every return iterate as a raw iterate, `.8` places the return
orbit in the finite core, `.9` records the consequent periodicity of that
orbit, and `.13` identifies the
attractor of the corner case. `.7` recovers the expansion of return cycles to
raw cycles, and `.14` sharpens `.7` in the corner case to the exact periodic
set.

**Difficulty decrease.** The infinite object is replaced by a self-map of the
finite core $\{1,\dots,c\}$: `.3` decreases the state above the core, so
`.8` bounds the descent by the seed itself, and `.9` reduces the remaining
behaviour to a pigeonhole argument on a finite set. The corner case collapses
the finite core to three states, whose return map is computed outright in
`.11`, so `.13` and `.14` need no search. The decreasing resource is the
state value above the core, and the change of representation is the return map
together with the domain-closed hypothesis that makes it realizable. The bound
$k\le n$ of `.8` makes the classification effective: a seed is decided by at
most $n$ return steps, each of them one or two instructions.

**Preservation conditions.** Every statement keeps $d\ge2$, $c\ge1$ and
positivity $1\le n$ where they are used; the corner statements add $d\ge3$
and record below why. Nothing here asserts a uniform core theorem for general
multipliers, the convergence of the original Collatz map, or any density
statement about the divergent set.

## Controls and excluded cases

- **Zero.** The state $0$ is a fixed point of every `CoreMap` and lies in the
  domain, so it is periodic without reaching the corner cycle. Positivity is
  therefore a hypothesis of `.13` and `.14`, not a convenience.
- **Offset zero.** The Lean statement `CoreReturnReachesCoreBounded` carries
  $c\ge1$ because its proof uses `CoreReturnPositive`; the return map itself
  still reaches the core at $c=0$, since it strictly decreases on positive
  states. The example $d=2$, $c=0$, `CoreMap 2 0 1 = 1` is a property of
  the raw map: the single affine instruction is the identity there.
- **Divisor two.** `CoreReturnCornerOne` and `CoreReturnCornerFixedUnique` need
  only $d\ge2$: their hypotheses are the ones used by the proofs, and the
  trap range `CoreMapCornerTrap` is stated for $d\ge3$. The classification
  needs $d\ge3$: at $d=2$, $c=3$ the state $2$ is accessible and the raw
  map carries the second cycle $1\mapsto4\mapsto2\mapsto1$ beside
  $3\mapsto6\mapsto3$, so `.13` would be false with two raw cycles.
- **Uniqueness scope.** `CoreReturnCornerFixedUnique` concerns fixed points of
  the return map; for $d\ge3$ the return orbit of $1$ leaves the accessible
  set at the trap $2$, which is exactly why `.13` classifies seeds rather than
  core states.
- **Density.** A natural-density statement for the divergent set is not proved
  here; the certificate records the opposite side of the count, namely that
  only a sparse set of seeds reaches the cycle. The function `CycleBasinCount`
  counts the seeds below a bound whose corner orbit reaches the two cycle, and
  `TestCycleBasinCounts` pins the counts below $300000$: $1977$ for $d=3$,
  $63$ for $d=4$, $57$ for $d=5$, $22$ for $d=6$, $31$ for $d=7$,
  $16$ for $d=9$, $15$ for $d=12$ and $10$ for $d=20$. Finite counting is
  not the density statement, and the density claim remains open.

## Formal dependencies

- `Foundations.Main.StartHere` supplies the iterate convention `Iterate` and
  the addition rule `IterateAdd`; the successor form used below is restated
  locally as `CoreIterateSucc`.
- `QCD.Scaling.001` and `QCD.TimeCompression.002` treat general multipliers and
  periods; the present family covers only $q=d-1$ and does not rederive
  them.
- `QCD.Additive.003` closes the $q=1$ slice, which is a different multiplier
  and is not claimed here.

## Go certificate contract

`go/RelationsCore.go` checks the statements above on bounded ranges with
machine arithmetic, and `go/RelationsCore_test.go` re-derives step values,
return-step values and return iterates on sampled parameters with `math/big`. The program prints

```
relation core checks: 186207, failures: 0
```

and exits nonzero on any failure. The total decomposes as
$77556+59708+780+11000+16000+260+20903$:

- domain sweep, $d\le8$, $c\le10$, $n\le600$: residue characterization,
  return realization, descent above the core and core invariance;
- core sweep, the same ranges: trap growth outside the domain, core
  reachability and periodicity inside it;
- corner sweep, $3\le d\le40$: the values `.11`, the trap range, the raw
  cycle `.12` and the control at $d=2$;
- classification sweep, $3\le d\le24$, seeds $\le500$: `.13`;
- periodic-point sweep, $3\le d\le12$, $k\le8$, $x\le200$: `.14`;
- expansion sweep, $d\le10$, $c\le12$, core seeds: `.7` for
  domain-closed returns and trap divergence otherwise;
- chunked sweep, $2\le d\le17$, $c\le8$, $n\le200$ over four workers,
  compared against a serial recomputation.

The bounded sweeps are not the theorems: the Lean statements above are the
proofs, and the program is a certificate of agreement on the stated ranges.
Every walk keeps its multiplier at most fifty-nine and stops at the guard
$2^{58}$, so machine words cannot wrap unnoticed; the guarded walks of the
program stay at multiplier at most twenty-three, and the corner sweep evaluates
a single step at multiplier thirty-nine. `TestSweepTotals` pins the
printed total, `TestParallelSweepAgrees` compares the chunked sweep with a
serial one, `TestWarmedOrbitAllocation` requires zero allocations after
warm-up, and `TestCacheSemantics` checks the memo of scheduled pairs; the
chunked sweep partitions the range into $d$-blocks, so each parameter pair is
reported once by construction.

## Build and checks

From the repository root:

```
lake build RelationsCore
CGO_ENABLED=0 go vet ./QCD.Relations.Core.001/go
CGO_ENABLED=0 go test -count=1 ./QCD.Relations.Core.001/go
make go GOFILE=QCD.Relations.Core.001/go/RelationsCore.go
```

Every declaration of `lean/RelationsCore.lean` depends only on `propext`,
`Classical.choice` and `Quot.sound`.
