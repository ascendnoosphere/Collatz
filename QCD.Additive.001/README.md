<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# QCD.Additive.001 — Additive access and finite cores

For $`c\ge1`$ and $`D\ge2`$, consider the positive raw map

```math
T(n)=\begin{cases}n/D,&D\mid n,\\n+c,&D\nmid n.\end{cases}
```

Put

```math
g=\gcd(c,D),\qquad L=D/g,\qquad
B=c(L-1),\qquad N=\left\lfloor\frac{B}{D-1}\right\rfloor.
```

## Access and exact raw blocks

If $`g\nmid n`$, no affine iterate is divisible by $`D`$. The full raw orbit is
$`T^{\circ j}(n)=n+jc`$, so it tends to infinity.

If $`g\mid n`$, exactly one $`0\le\ell<L`$ satisfies $`D\mid n+\ell c`$. All earlier
states in this affine run are nondivisible. The first-division map is

```math
H(n)=\frac{n+\ell c}{D},\qquad T^{\circ(\ell+1)}(n)=H(n).
```

This block contains $`\ell`$ additions followed by one division, including the
case $`\ell=0`$. It does not combine all consecutive divisions.

## Finite core and reconstruction

Every accessible endpoint satisfies

```math
D\,H(n)\le n+B.
```

Consequently $`H(n)<n`$ above $`N`$, and $`H(n)\le N`$ for accessible $`n\le N`$.
Also $`N\le c`$. Every positive raw seed therefore reaches either an
inaccessible state or a positive state at most $`N`$.
Above this finite set the endpoint strictly decreases; within it every
accessible first-division edge remains in it. Each edge reconstructs its
original additions and division with the exact raw clock.

When $`g=1`$, every state is accessible and $`N=c`$; all positive seeds reach
this finite first-division core. When $`N=0`$, every positive seed reaches an
inaccessible state and its full raw orbit tends to infinity.

## Geometric entry bound

Define the signed shifted coordinate and its positive boundary increment by

```math
\delta(n)=(D-1)n-B,\qquad \epsilon=\delta(N+1).
```

Then $`1\le\epsilon\le D-1`$, and each accessible edge satisfies
$`D\delta(H(n))\le\delta(n)`$. After $`h`$ legal first-division edges,

```math
D^h\delta(n_h)\le\delta(n_0).
```

If $`D^h\epsilon>\delta(n_0)`$, the last endpoint is at most $`N`$. Thus the least
such integer $`h`$ bounds the number of edges before core entry or trapping.
The corresponding raw time is at most $`hL`$. The exponent bound is computed
with exact integer powers, not floating-point logarithms.

## Formal development

[Additive.lean](lean/Additive.lean) uses the shared `PositiveRawStep` and proves:

- `AdditiveFirstDivisionExists` and `AdditiveAccessUnique`: complete access
  criterion and the unique access index;
- `AdditiveFirstDivisionGuards`, `AdditiveFirstDivisionPrefix`, and
  `AdditiveFirstDivisionRaw`: every guard and the exact raw block;
- `AdditiveTrapIterate`, `AdditiveTrapEscape`, and
  `AdditiveReachedTrapEscape`: exact affine tails and full-sequence escape;
- `AdditiveAboveCoreDescent`, `AdditiveCoreInvariant`, and
  `AdditiveCoreRadiusLe`: strict descent, core invariance, and radius control;
- `AdditiveFiniteReduction` and `AdditiveZeroCoreEscape`: all-seed raw recovery
  and the empty-core case;
- `AdditiveCoprimeCore` and `AdditiveCoprimeCapture`: the full coprime core;
- `AdditivePathDefect`, `AdditiveCoreDefectBounds`, and
  `AdditiveGeometricEntry`: the exact geometric threshold; and
- `AdditivePathRawRecovery`, `AdditivePathClockUpper`,
  `AdditiveGeometricRawEntry`, and `AdditiveFiniteBudget`: path recovery and
  unconditional core-or-trap entry at the original clock.

The arithmetic lemmas also allow zero offset; the escape results explicitly
require a positive offset. No signed-state or negative-divisor claim is made.
This result gives a finite reduction. [QCD.Additive.002](../QCD.Additive.002/README.md)
classifies its positive cycles and recovers their exact primitive raw periods.

## Exact computation

[Additive.go](go/Additive.go) computes the access index by modular inversion,
checks strict endpoint descent, and records the first core-or-trap endpoint,
its exact raw time, edge count, and least geometric budget. Parameters, states, raw times, and arithmetic values use arbitrary precision.
Edge counts and geometric exponents use `uint64`, with oversized budgets rejected. Verification recomputes all fields without changing
the supplied certificate.

The executable checks every $`1\le c\le32`$, $`2\le D\le48`$, and $`1\le n\le128`$:
$`32\cdot47\cdot128=192{,}512`$ bounded certificates. The large seed $`53\cdot37^{300}`$
with $`c=1`$, $`D=37`$ reaches the core state $`1`$ in exactly $`302`$
first-division edges and $`358`$ raw instructions. Finite execution checks the
implementation; the Lean and written proofs establish the universal claims.

Tests include an independent machine-word residue scan, original raw replay,
trap tails, all-field tampering, ownership and direct aliases, nil validation,
raw times beyond 64 bits, multiword zero-core parameters, and a warmed
zero-allocation build-and-verify path.

```bash
lake env lean QCD.Additive.001/lean/Additive.lean
make go GOFILE=QCD.Additive.001/go/Additive.go
go test ./QCD.Additive.001/go
make tex TEXFILE=QCD.Additive.001/tex/Additive.tex
```
