<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# QCD.Additive.003 — Positive additive all-seed outcomes

## Statement and domain

Fix **exactly** $q=1$, an integer offset $c\ge1$, and a divisor $D\ge2$.
For positive seeds, the original raw map is
$$
C(n)=\begin{cases}n/D,&D\mid n,\\n+c,&D\nmid n.\end{cases}
$$
Put
$$
g=\gcd(c,D),\quad L=D/g,\quad B=c(L-1),\quad
N=\left\lfloor\frac{B}{D-1}\right\rfloor.
$$
Every positive seed has exactly one outcome: eventual raw periodicity, or a
finite entry into an inaccessible phase $g\nmid r$ with the exact raw tail
$r+jc$, tending to infinity along the full sequence.
Furthermore,
$$
\text{every positive seed is eventually periodic}
\quad\Longleftrightarrow\quad \gcd(c,D)=1.
$$
Initial accessibility is not a sufficient per-seed basin criterion.

[Detailed proofs](tex/AdditiveOutcome.tex) ·
[Formal proofs](lean/AdditiveOutcome.lean) ·
[Exact outcome certificates](go/AdditiveOutcome.go) ·
[Certificate tests](go/AdditiveOutcome_test.go) ·
[Access and finite cores](../QCD.Additive.001/README.md) ·
[Complete cycle classification](../QCD.Additive.002/README.md)

## Numbered results

| Result | Claim | Principal Lean theorem |
|---|---|---|
| QCD.Additive.003.1 | Every positive core phase reaches a true trap or a positive raw return with both clocks at most $NL$. | `AdditiveCoreOutcome` |
| QCD.Additive.003.2 | Every positive seed is eventually periodic or has an exact escaping affine tail. | `AdditiveAllSeedOutcome` |
| QCD.Additive.003.3 | A geometric entry budget $h$ gives a common outcome phase $u\le(h+N)L$ and return length $0<p\le NL$; $h=n$ is always admissible. | `AdditiveAllSeedTotalBudget`, `AdditiveSeedGeometricBudget`, `AdditiveAllSeedExplicitBudget` |
| QCD.Additive.003.4 | Eventual periodicity is equivalent to never reaching a trap; full-sequence escape is equivalent to reaching one. | `AdditivePeriodicIffNoTrap`, `AdditiveEscapeIffTrap` |
| QCD.Additive.003.5 | Every positive seed is eventually periodic if and only if $\gcd(c,D)=1$. | `AdditiveAllPeriodicIffCoprime` |
| QCD.Additive.003.6 | Every positive seed escapes if and only if there is no positive raw periodic state; an empty cycle window is sufficient. | `AdditiveEverySeedEscapesIffNoCycle`, `AdditiveEmptyWindowEscape` |
| QCD.Additive.003.7 | Nonempty cores, positive windows, and initial access need not imply a periodic basin. | `AdditiveNonemptyCoreEscapeControl`, `AdditivePositiveWindowEscapeControl`, `AdditiveMixedBasinControl` |

The arithmetic event, return-or-trap, and finite-budget lemmas also allow
$c=0$. This is a separately stated boundary: an inaccessible phase is then
fixed, not escaping. The positive-offset escape and coprimality criteria above
require $c>0$. No result applies to a multiplier other than $q=1$.

## Reduction and recovery

**Original obligation:** classify an unbounded positive raw trajectory,
including its entire raw clock and full-sequence escape behavior.

**Replacement obligations:** execute legal first-division events, strictly
reduce the positive endpoint above $N$, and classify a finite functional
graph on at most $N$ positive core states, with inaccessible phases stopped.

**Recovery:** an accessible event has unique $0\le\ell<L$, quotient
$(n+\ell c)/D$, and exact raw cost $\ell+1$. A trap is certified before
recording or advancing it; its exact tail is $r+jc$. Equal accessible event
phases give a strictly positive difference of accumulated raw clocks. The
same seed, core-entry witness, and return/trap witness are used throughout.

**Actual decrease:** positive integers strictly decrease above the core; the
remaining event graph has the explicit finite size $N\le c$. A computable
geometric entry budget and at most $N$ additional events bound the residual
work. This does not assume a global bounded raw orbit or an unknown stopping
time. Finite-state recognition alone would be unsound if zero-clock stopped
traps were accepted as raw cycles.

**Preservation:** division precedence, all predivision guards, positivity,
exact accumulated raw clocks, and the original positive-offset domain are
retained. The common-witness bounds are
$$
\delta(n)<D^h\epsilon,\quad
\delta(x)=(D-1)x-B,\quad \epsilon=\delta(N+1)\in[1,D-1],
$$
$$
u\le(h+N)L,\qquad 0<p\le NL\quad\text{in the return case}.
$$
Bernoulli gives $\delta(n)<D^n\epsilon$, hence the explicit fallback
$u\le(n+N)L$. These are numeric-parameter bounds, not uniform polynomial
bit-complexity statements.

The no-cycle criterion is executable together with the complete whole-orbit
test in `QCD.Additive.002`. A truncated enumeration, a nonempty raw core, or a
positive window by itself is not a decision certificate.

## Go certificate contract

`NewMap` copies its positive offset and divisor; the resulting map is
immutable. Its zero value is invalid. `AllSeedsPeriodic` implements the
universal gcd criterion, and `CoreRadius` copies the exact bound.

`Classify(seed, limits, cache, workspace, output)` either produces a true trap
or positive raw-return certificate, or returns an error. `ErrResource` means
**no new classification** was certified under the requested event or dense
core-memory limits. Any error leaves the output values unchanged; a retained
older certificate must not be treated as a certificate for the failed call.
A zero-event initial trap can be certified with zero event and core budgets.

A certificate owns:

- its positive `Seed` and `Phase`;
- its exact nonnegative raw prefix `Clock`;
- its `Period`, zero for a trap and positive for a return;
- the machine-sized total and prefix event counts;
- the `Trap` or `Periodic` tag.

The claimed equation in the return case is
$$
C^{\mathtt{Clock}+\mathtt{Period}}(\mathtt{Seed})=
C^{\mathtt{Clock}}(\mathtt{Seed})=\mathtt{Phase}.
$$
The verifier checks legal first-division events independently of the search
cache and does not assert least period. It rejects invalid headers, stopped
traces pretending to advance, false trap tags, and wrong phases or clocks.
Its explicit event bound is separate from the certificate's integer widths.
For $c=1,D=2^{200},n=1$, one event has a 201-bit raw period $D$;
verification does not literally replay its $D-1$ affine instructions.

Each caller owns a reusable `Workspace` and `Cache`. Dense clock entries have
disjoint backing storage. Map inputs and returned certificate fields are
copied; direct input aliases with output fields are supported. Shallow copies
of `big.Int`, concurrent sharing of scratch/cache storage, and manual mutation
of private map fields are unsupported. `Accessible`, `Event`, `Store`, and
`Warm` are internal helpers with the documented initialization preconditions.
Dense core allocation is attempted only after accessible core entry.

The program partitions independent divisor ranges into four half-open
chunks, with a separate workspace/cache and result slot for every worker.
It checks 94,208 bounded outcomes against original raw instructions and checks
one 201-bit raw-period certificate. Tests independently traverse the raw map
and compare least raw periods in that bounded box, inject malformed
certificates, test ownership and refusal, and measure zero allocation for a
warmed one-state small event. This measured small case is not a universal
allocation claim for arbitrary-width standard-library arithmetic.

## Controls

- $(c,D)=(9,6)$: $N=1$, but the modular cycle window is empty; all seeds escape.
- $(c,D)=(10,4)$: the window radius is one, but its only representative leaves
  the window under the inverse permutation; all seeds escape.
- $(c,D)=(6,4)$: $2\to8\to2$ is periodic, while $4\to1$ reaches the
  escaping tail $1+6j$, despite initial access.
- $c=0$ is not an escape extension: the
  [unit homogeneous fixed-point theorem](../QCD.Homogeneous.003/README.md) applies.

## Formal dependencies

The three stopped-event definitions are `AdditiveEventIndex`,
`AdditiveEventStep`, and `AdditiveEventWeight`. Their exact access, endpoint,
core, and clock properties are proved by `AdditiveEventIndexSpec`,
`AdditiveEventRaw`, `AdditiveEventRecovery`, `AdditiveEventCore`,
`AdditiveEventCoreTrace`, `AdditiveEventWeightUpper`, `AdditiveEventClockUpper`,
`AdditiveEventClockMonotone`, and `AdditiveEventCoreRepeat`.

The common-witness assembly is `AdditiveAllSeedReturnOrTrap` and
`AdditiveAllSeedFiniteBudget`. The incompatibility and domain lemmas are
`AdditivePeriodicNoTrap`, `AdditivePeriodicNotEscape`, `AdditiveRawPositive`,
and `AdditiveRawIteratePositive`. Together with the principal theorem table,
these name every owned theorem in the module.

## Build and checks

From the repository root:

```sh
make lean
make go GOFILE=QCD.Additive.003/go/AdditiveOutcome.go
CGO_ENABLED=0 go test ./QCD.Additive.003/go
CGO_ENABLED=0 go vet ./QCD.Additive.003/go
make tex TEXFILE=QCD.Additive.003/tex/AdditiveOutcome.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```

Finite examples are checks of the implementation. The universal conclusions
come from the formal proofs and the explicit recovery argument.
