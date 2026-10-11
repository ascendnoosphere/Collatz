<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# QCD.Additive.001 — Additive access and finite cores

For `c ≥ 1` and `D ≥ 2`, consider the positive raw map

```text
T(n) = n / D  if D divides n,
       n + c  otherwise.
```

Put

```text
g = gcd(c,D),    L = D/g,
B = c(L−1),     N = floor(B/(D−1)).
```

## Access and exact raw blocks

If `g ∤ n`, no affine iterate is divisible by `D`. The full raw orbit is
`T^[j](n) = n + jc`, so it tends to infinity.

If `g | n`, exactly one `0 ≤ ell < L` satisfies `D | n + ell c`. All earlier
states in this affine run are nondivisible. The first-division map is

```text
H(n) = (n + ell c)/D,
T^[ell+1](n) = H(n).
```

This block contains `ell` additions followed by one division, including the
case `ell = 0`. It does not combine all consecutive divisions.

## Finite core and reconstruction

Every accessible endpoint satisfies

```text
D H(n) ≤ n + B.
```

Consequently `H(n) < n` above `N`, and `H(n) ≤ N` for accessible `n ≤ N`.
Also `N ≤ c`. Every positive raw seed therefore reaches either an
inaccessible state or a positive state at most `N`.
Above this finite set the endpoint strictly decreases; within it every
accessible first-division edge remains in it. Each edge reconstructs its
original additions and division with the exact raw clock.

When `g = 1`, every state is accessible and `N = c`; all positive seeds reach
this finite first-division core. When `N = 0`, every positive seed reaches an
inaccessible state and its full raw orbit tends to infinity.

## Geometric entry bound

Define the signed shifted coordinate and its positive boundary increment by

```text
delta(n) = (D−1)n − B,
epsilon = delta(N+1).
```

Then `1 ≤ epsilon ≤ D−1`, and each accessible edge satisfies
`D delta(H(n)) ≤ delta(n)`. After `h` legal first-division edges,

```text
D^h delta(n_h) ≤ delta(n_0).
```

If `D^h epsilon > delta(n_0)`, the last endpoint is at most `N`. Thus the least
such integer `h` bounds the number of edges before core entry or trapping.
The corresponding raw time is at most `hL`. The exponent bound is computed
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
This result gives a finite reduction, not an enumeration of its cycles.

## Exact computation

[Additive.go](go/Additive.go) computes the access index by modular inversion,
checks strict endpoint descent, and records the first core-or-trap endpoint,
its exact raw time, edge count, and least geometric budget. Parameters, states, raw times, and arithmetic values use arbitrary precision.
Edge counts and geometric exponents use `uint64`, with oversized budgets rejected. Verification recomputes all fields without changing
the supplied certificate.

The executable checks every `1 ≤ c ≤ 32`, `2 ≤ D ≤ 48`, and `1 ≤ n ≤ 128`:
`32 · 47 · 128 = 192,512` bounded certificates. The large seed `53 · 37^300`
with `c = 1`, `D = 37` reaches the core state `1` in exactly `302`
first-division edges and `358` raw instructions. Finite execution checks the
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
