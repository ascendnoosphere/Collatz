<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# QCD.Homogeneous.003 — Unit-multiplier homogeneous classification

## Statement

For an integer divisor `D ≥ 2`, consider the positive raw map

```text
T_D(n) = n / D  if D divides n,
         n      otherwise.
```

Every positive seed has a unique whole-base decomposition

```text
n = r D^k,    D ∤ r.
```

The raw orbit is exactly

```text
T_D^[j](n) = r D^(k-j),
```

where natural-number subtraction is truncated at zero. Consequently:

- the orbit first reaches `r` at raw time `k`;
- `r` is fixed, and every later state equals `r`;
- the positive fixed points are exactly the positive integers not divisible
  by `D`;
- every positive periodic orbit is a one-point fixed orbit; and
- every raw iterate is at most the initial seed.

Zero is also fixed by division precedence, but the canonical positive
factorization and exact-entry theorem are stated for positive seeds.

## Canonical reconstruction

For `q = 1`, `c = 0`, and `D ≥ 2`, the unique pair `(r,k)` with
`n = r D^k` and `D ∤ r` determines the complete positive raw orbit. The identity

```text
T_D^[j](n) = r D^(k-j)
```

reconstructs every state at the original raw clock and proves exact first
entry, rather than only eventual entry.

Before entry, the remaining exponent is positive and drops by one at every
raw step. It reaches zero after exactly `k` steps, and the resulting base-free
state is fixed.

The result concerns unit multipliers, zero offset, and positive seeds. It does
not treat positive offsets, multipliers at least two, signed states, or
negative divisors. Since every positive `D`-free integer is fixed, there are
infinitely many positive fixed points; no finite attractor is claimed.

## Lean development

`lean/UnitHomogeneous.lean` imports the shared positive homogeneous map and
proves:

- `UnitStepRepresentation`: one raw step subtracts one available whole-base
  exponent;
- `UnitExponentIterate`: repeated exponent updates give truncated subtraction;
- `UnitIterateRepresentation`: exact raw iterates from base-free normal form;
- `UnitNormalFormUnique`: uniqueness of the whole-base canonical data;
- `UnitSeedIterateRepresentation`: canonical exact iterates for every positive
  seed;
- `UnitZeroFixed` and `UnitBaseFreeFixed`: the zero and positive base-free
  boundaries;
- `UnitPositiveFixedIff`: complete positive fixed-point classification;
- `UnitPositivePeriodicIffFixed`: every positive-period return occurs at a
  base-free fixed point;
- `UnitNoEarlyFixed` and `UnitEventuallyFixed`: exact first entry and fixed
  tail; and
- `UnitStepLe` and `UnitIterateLe`: source-relative height control.

The canonical factor and exponent use Mathlib's whole-base decomposition API,
so composite divisors retain their correct meaning. No prime factorization is
introduced.

## Executable certificates

`go/UnitHomogeneous.go` uses arbitrary-precision integers. A certificate stores
the seed, canonical fixed factor, and exact entry time. Verification recomputes
the decomposition, replays every strict pre-entry step, checks entry at the
claimed time, and checks the fixed tail without mutating the certificate.

The executable verifies:

- every `2 ≤ D ≤ 96` and `1 ≤ n ≤ 4096`, totaling
  `95 · 4096 = 389,120` certificates; and
- the seed `53 · 37^300`, whose exact entry time is `300` and whose fixed
  factor is `53`.

The tests add an independent machine-word decomposition over a bounded family,
composite-divisor branch checks, in-place stepping, tamper rejection,
validation boundaries, and a warmed zero-allocation build-and-verify path.
Finite execution validates the implementation; the Lean and written proofs
establish the universal theorem.

Run from the repository root:

```bash
lake env lean QCD.Homogeneous.003/lean/UnitHomogeneous.lean
make go GOFILE=QCD.Homogeneous.003/go/UnitHomogeneous.go
go test ./QCD.Homogeneous.003/go
make tex TEXFILE=QCD.Homogeneous.003/tex/UnitHomogeneous.tex
```
