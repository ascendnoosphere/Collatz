<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# QCD.OffsetObstruction.001 — Gcd strata of the positive offset map

## Statement and domain

Fix an offset $c\ge0$ and consider the positive-offset map on natural numbers
$$
C(n)=\begin{cases}n/2,&2\mid n,\\3n+c,&2\nmid n.\end{cases}
$$

Let $m\mid c$ with $\gcd(m,6)=1$. Then every step preserves the gcd with
$m$:
$$
\gcd(C(n),m)=\gcd(n,m),
$$
and therefore every orbit stays in the stratum of its seed,
$$
\gcd(C^{k}(n),m)=\gcd(n,m)\qquad\text{for all }k\ge0.
$$
If in addition $m>1$ and $\gcd(n,m)=1$, then no iterate of $n$ equals
$c$, $4c$, or $2c$. For odd $c$ those three states form the cycle
$$
c\longmapsto 4c\longmapsto 2c\longmapsto c .
$$
The multiples of $m$ below $N$ number at most $N/m+1$, and hence
$$
m\cdot\#\{0\le n<N:m\mid n\}\le N+m,
$$
so the stratum of multiples of $m$ has upper density at most $1/m$. For even $c$ every positive
seed is unbounded: the dyadic prefix is consumed exactly and odd states grow by
at least one per step. Finally, the offset $3^{a}$ scales the offset-one
dynamics by the same power of three.

[Detailed proofs](tex/OffsetObstruction.tex) ·
[Formal proofs](lean/OffsetObstruction.lean) ·
[Exact offset certificates](go/OffsetObstruction.go) ·
[Certificate tests](go/OffsetObstruction_test.go) ·
[Multiplicatively independent homogeneous maps](../QCD.Homogeneous.001/README.md) ·
[Positive additive access](../QCD.Additive.001/README.md)

## Numbered results

| Result | Claim | Principal Lean theorem |
|---|---|---|
| QCD.OffsetObstruction.001.1 | If $m\mid c$ and $\gcd(m,6)=1$, then $\gcd(C(n),m)=\gcd(n,m)$ for every $n$. | `OffsetStepGcd`, `OffsetTwoMulGcd` |
| QCD.OffsetObstruction.001.2 | Every orbit stays in the gcd stratum of its seed. | `OffsetOrbitStratum` |
| QCD.OffsetObstruction.001.3 | For odd $c$, the states $c$, $4c$, $2c$ form a three-step cycle. | `OffsetCycleStepSelf`, `OffsetCycleStepFour`, `OffsetCycleStepTwo`, `OffsetCycle` |
| QCD.OffsetObstruction.001.4 | If $m>1$, $m\mid c$, $\gcd(m,6)=1$, and $\gcd(n,m)=1$, then no iterate of $n$ is $c$, $4c$, or $2c$. | `OffsetCoprimeSeedAvoidsCycle` |
| QCD.OffsetObstruction.001.5 | The multiples of $m$ below $N$ number at most $N/m+1$, and $m$ times that count is at most $N+m$. | `OffsetMultipleCountLe`, `OffsetMultipleDensity` |
| QCD.OffsetObstruction.001.6 | For even $c$, an odd state has an odd strictly larger successor, oddness persists, and an odd seed reaches at least $n+j$ at time $j$. | `OffsetEvenOffsetOddStep`, `OffsetEvenOffsetOddPersist`, `OffsetEvenOffsetGrowthLower` |
| QCD.OffsetObstruction.001.7 | For every $c$, $u$, and $v$, the dyadic prefix is exact: $C^{v}(2^{v}u)=u$. | `OffsetHalvePrefix` |
| QCD.OffsetObstruction.001.8 | For even $c$, every positive seed is unbounded. | `OffsetEvenOffsetUnbounded` |
| QCD.OffsetObstruction.001.9 | The offset $3^{a}$ scales the offset-one dynamics by $3^{a}$, at every iterate. | `OffsetStepScaling`, `OffsetIterateScaling` |
| QCD.OffsetObstruction.001.10 | Starting one step later is the same as iterating the successor once: $C^{k+1}(n)=C^{k}(C(n))$. | `OffsetIterateSuccFirst` |

The degenerate cases are included: $0$ is even and fixed, and for $m=1$
the stratum condition is vacuous. All statements are over the natural numbers.
No statement concerns offsets whose every divisor coprime to $6$ equals
$1$, such as $c=3^{a}$: there only the trivial modulus $m=1$ survives,
and result .9 describes the $3^{a}$-scaled offset-one dynamics without
identifying the two maps.

## Reduction and recovery

**Original obligation:** for the positive-offset map with $c=3^{a}m$ and
$\gcd(m,6)=1$, determine whether an orbit can leave its gcd stratum, decide
whether a seed coprime to $m$ can reach the odd short cycle, bound the density
of the states that the cycle can capture, and settle the fate of positive seeds
for even $c$.

**Replacement obligations:** one-step gcd algebra under $m\mid c$ and
$\gcd(m,6)=1$; the finite three-step computation of the cycle; a counting
bound for multiples in an initial segment; and a two-case growth estimate for
even offsets.

**Recovery:** the one-step identity telescopes along the orbit
(`OffsetOrbitStratum`). A seed coprime to $m$ keeps gcd $1$ with $m$ at
every time, while $c$, $4c$, $2c$ are all multiples of $m$, so the cycle
is unreachable (`OffsetCoprimeSeedAvoidsCycle`). The basin of the cycle
$c,4c,2c$ is contained in the multiples of $m$, whose counting bound gives
upper density at most
$1/m$ (`OffsetMultipleDensity`). For even $c$ the factorization
$n=2^{v}u$, $u$ odd, lets the exact dyadic prefix (`OffsetHalvePrefix`)
reduce unboundedness to the strictly increasing odd dynamics
(`OffsetEvenOffsetOddStep`, `OffsetEvenOffsetGrowthLower`).

**Actual decrease:** each obligation is a finite algebraic or counting
computation. The only unbounded quantity is the number of iterates, and it is
handled by the explicit lower bound $n+j$, not by a search: no stopping time
is assumed and no bounded orbit is hypothesized. The density bound is proved by
an injection into $\{0,\dots,\lfloor N/m\rfloor\}$, not by an estimate of a
basin after the fact.

**Preservation:** the map is used literally, with the even case first. Raw
states, division precedence, and the offset $c$ itself are retained;
no averaged, accelerated, or rescaled map replaces $C$ in the numbered
statements. The scaling identity is stated as a separate result about the
family $C$ with offset $3^{a}$, and the two offsets are not identified.

## Controls

- $c=1$, $m=5$: $m\nmid c$ and the stratum condition fails at $n=3$,
  since $C(3)=10$ and $\gcd(10,5)=5\ne1=\gcd(3,5)$.
- $c=3$, $m=3$, $n=1$: $m\mid c$ but $\gcd(m,6)=3$, and the
  invariance fails: $C(1)=6$ and $\gcd(6,3)=3\ne1=\gcd(1,3)$.
- $c=5$, $m=5$: the seed $1$ is coprime to $m$, so $1$ is never
  $5$, $20$, or $10$; the seed $5$ is periodic, and $5$ is a
  multiple of $m$.
- $c$ even, seed $1$: odd forever, so the orbit is $1,3+c,9+4c,\dots$
  and is unbounded; in contrast, for odd $c$ the seed $c$ is periodic.
  An odd offset need not have unbounded orbits.
- $c=0$: the map is $n\mapsto n/2$ on even and $n\mapsto3n$ on odd
  inputs, the homogeneous map $T_{3,2}$ of the multiplicatively independent
  family. Every divisor of $0$ is admissible, so the numbered results apply
  at $c=0$ with a vacuous gcd identity.

## Formal dependencies

The module imports `GeneralizedCollatz` for `Iterate` and `IterateAdd`, and
uses Mathlib divisibility, gcd, parity, finite-cardinality, and factorization
lemmas. `OffsetIterateSuccFirst` is proved locally, since the iterate-shift
identity is not imported from another family. Every declaration listed above is
an owned theorem of `lean/OffsetObstruction.lean`.

## Go certificate contract

`Step` mirrors the map on machine words and `Gcd`, `Pow3` provide the
arithmetic used by the checks. A `Workspace` owns one reusable orbit buffer;
`Orbit` fills it for a bounded horizon, and a warmed traversal of a fixed
horizon allocates nothing. A `Cache` records verified moduli.

`StratumPreserved` returns the first state `n` at which a single step changes the
gcd with `m`, together with that state; the other predicates, `OrbitStratumPreserved`,
`CycleWitness`, `AvoidsCycle`, `MultiplesBelow`, `DensityHolds`,
`HalvingPrefix`, `Reaches`, and `ScalingHolds`, are bounded checks of the exact
statements. `parallelStratumSweep` partitions the offsets into four contiguous
fifty-wide blocks covering `1..200`, with one workspace per worker and a
mutex-protected aggregate; every pair contributes one one-step check and eight
orbit checks. The entry point prints `offset obstruction checks: 139412,
failures: 0` on the recorded sweep, a finite run output and not a proof.

All Go quantities are `uint64`; a horizon or a bound is a finite computational
limit, not a proof. Refusals and negative controls are reported rather than
silently dropped, and the universal claims are those of the Lean module.

## Build and checks

From the repository root:

```sh
make lean
make go GOFILE=QCD.OffsetObstruction.001/go/OffsetObstruction.go
CGO_ENABLED=0 go test ./QCD.OffsetObstruction.001/go
CGO_ENABLED=0 go vet ./QCD.OffsetObstruction.001/go
make tex TEXFILE=QCD.OffsetObstruction.001/tex/OffsetObstruction.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```

The finite sweeps and the negative controls check the implementation of the
statements. The universal conclusions are the formal proofs above.
