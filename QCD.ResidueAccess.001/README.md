# Accessible residues of a divisor slice

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

For integers $`q\ge2`$, $`c\ge1`$ and $`D\ge2`$ the divisor slice of the raw
map sends

```math
n\longmapsto \begin{cases} n/D, & D\mid n,\\ qn+c, & D\nmid n,\end{cases}
```

and its residue dynamics is the affine map on $`\mathbb{Z}/D\mathbb{Z}`$

```math
F(r)=qr+c \bmod D .
```

Every residue reached from $`0`$ either returns to $`0`$ or enters a cycle
that avoids $`0`$; when $`\gcd(q,D)=1`$ the return is guaranteed and the
accessible residues are precisely the orbit of $`0`$ under $`F`$. This
family classifies that orbit. The affine offset after $`j`$
steps is the repunit sum $`G_j(q)=1+q+\dots+q^{j-1}`$, the return criterion is
governed by the access modulus

```math
M(q,c,D)=\frac{D(q-1)}{\gcd\bigl(c,\,D(q-1)\bigr)},
```

and when the walk returns, its return time is the multiplicative order of
$`q`$ modulo $`M`$ (rows .5 and .9). The
prime case splits: modulo a prime $`p`$ with $`p\nmid c`$ the orbit returns
after $`j`$ steps exactly when $`p\mid G_j(q)`$, and the return time is
$`p`$ exactly when $`q\equiv1\pmod p`$, while for $`q\not\equiv1\pmod p`$
with $`\gcd(p,q)=1`$ it is smaller than $`p`$.

## Statements

| # | Statement | Carry |
|---|-----------|-------|
| .1 | The residue walk: `AccessStep q c D r = (q*r + c) % D` starts at zero, steps by the affine map, and splits any block of steps into consecutive blocks. | `AccessStep`, `AccessOrbit`, `AccessOrbitZero`, `AccessOrbitSucc`, `AccessOrbitAdd` |
| .2 | **Closed form.** After $`j`$ steps the orbit of zero is $`c\,G_j(q)\bmod D`$. | `AccessOrbitEqOffsetMulRepunit` |
| .3 | The orbit of zero returns to zero after $`j`$ steps exactly when $`D\mid c\,G_j(q)`$. | `AccessOrbitEqZeroIff` |
| .4 | **Gcd reduction.** For $`X\ge0`$, $`D(q-1)\mid cX`$ exactly when $`M(q,c,D)\mid X`$. | `AccessModulusDvdIffMul` |
| .5 | **Return criterion.** The orbit of zero returns after $`j`$ steps exactly when $`M(q,c,D)\mid q^{j}-1`$. | `AccessOrbitEqZeroIffModulus` |
| .6 | The access modulus divides $`D(q-1)`$; when $`D`$ is coprime to $`q`$ it is itself coprime to $`q`$. | `AccessModulusDvdMulPred`, `AccessModulusCoprimeQ` |
| .7 | **Injectivity.** If $`D`$ is coprime to $`q`$, the residue map agrees on two residues exactly when they are congruent modulo $`D`$. | `AccessStepEqIff` |
| .8 | Blocks commute: iterating $`m`$ steps and then $`j`$ steps equals iterating $`m+j`$ steps, and the two blocks of the walk commute. | `AccessOrbitAdd`, `AccessIterateComm` |
| .9 | **Period.** If $`m`$ is the least positive exponent with $`M(q,c,D)\mid q^{m}-1`$, the orbit returns to zero at $`m`$, at every multiple of $`m`$, and at no other index. | `AccessOrbitEqZeroOfLeast`, `AccessOrbitPeriod`, `AccessOrbitPeriodMul`, `AccessOrbitEqZeroIffDvd` |
| .10 | The first $`m`$ values of the orbit are pairwise distinct, hence $`m\le D`$. | `AccessOrbitDistinct`, `AccessOrbitCardLe` |
| .11 | Every accessible residue is reached at a unique index below $`m`$. | `AccessOrbitRepresentative` |
| .12 | When the multiplier is one, the repunit sum is congruent to its length: $`G_j(q)\equiv j\pmod D`$ when $`q\equiv1\pmod D`$. | `AccessRepunitSumModeqIndex` |
| .13 | **Prime case, multiplier not one.** For a prime $`p`$ with $`p\nmid c`$ and $`q\not\equiv1\pmod p`$, the orbit returns after $`j`$ steps exactly when $`p\mid q^{j}-1`$. | `AccessPrimeOrbitIff` |
| .14 | **Prime case, multiplier one.** For a prime $`p`$ with $`p\nmid c`$ and $`q\equiv1\pmod p`$, the orbit returns after $`j`$ steps exactly when $`p\mid j`$. | `AccessPrimeOrbitIffIndex` |
| .15 | **Full access at a prime.** For a prime $`p`$ with $`p\nmid c`$ and $`q\equiv1\pmod p`$, the return time is $`p`$, and every residue modulo $`p`$ is visited by the orbit of zero. | `AccessPrimeFullAccess`, `AccessPrimeOrbitSurjective` |
| .16 | **Necessity at a prime.** For a prime $`p`$ with $`p\nmid c`$, $`p`$ coprime to $`q`$ and $`q\not\equiv1\pmod p`$, the return time is smaller than $`p`$, so some residue is inaccessible. | `AccessPrimeNotFullAccess` |

## Reduction and recovery record

**Original obligation.** Classify the residues accessible from $`0`$ under the
affine residue map of a divisor slice, and decide when the orbit exhausts all
residues modulo $`D`$.

**Replacement obligations.**

1. Compute the affine offset after $`j`$ steps in closed form (rows .1–.2).
2. Replace the divisibility condition $`D\mid c\,G_j(q)`$ by a condition on
   $`q^{j}-1`$ alone (rows .3–.6).
3. Prove that the orbit is periodic with least period $`m`$, that its first
   $`m`$ values are distinct, and that $`m\le D`$ (rows .7–.11).
4. Resolve the prime case: reduce the criterion to the order of $`q`$ modulo
   $`p`$ and identify when that order is $`p`$ (rows .12–.16).

**Recovery.** An orbit return is decided by row .5, so the accessible set is
the orbit of $`0`$ for $`m`$ steps, and row .11 shows that this set is exactly
the period-$`m`$ cycle containing $`0`$. Exhaustion modulo $`D`$ is full access
$`m=D`$; rows .15 and .16 decide it modulo a prime.

**Difficulty decrease.** The raw orbit analysis is replaced by a finite
divisibility question in $`\mathbb{Z}/M(q,c,D)\mathbb{Z}`$: the least exponent
$`m`$ with $`M\mid q^{m}-1`$ is computed once, and all orbit questions become
questions about $`m`$ (rows .5, .9, .11). No trajectory bound is assumed; the
bound $`m\le D`$ is derived by counting the distinct residues (row .10).

**Preservation conditions.** Rows .1–.3 and .8 hold for all $`q,c,D`$; row .12
assumes only $`q\equiv1\pmod D`$, and its modulus need not be prime. Rows
.4–.6, .9–.11, .13 and .15–.16 assume $`q\ge2`$ and $`D>0`$; row .7 assumes
$`D>0`$ and $`\gcd(q,D)=1`$, and the coprimality clause of row .6 adds the same
hypothesis. The prime rows assume $`p`$ prime and $`p\nmid c`$; rows .14 and
.15 add $`q\equiv1\pmod p`$, rows .13 and .16 the negation, and row .16 also
$`\gcd(p,q)=1`$ together with the existence of the least positive return time
$`m`$. Coprimality of $`q`$ and $`D`$ is used by the modulus coprimality clause
of row .6 and by the injectivity of row .7; the exhaustion statements do not
use it.

**Not formalized.** The identification of the accessible residues above with
the first-division residues of the raw map, the density-one escape when the
leakage $`m<D`$ is positive, the entry bound of the contracting return core,
the refinement at $`c=1`$ where the captured set has density zero, the
Hull–Dobell criterion for general cycles, the general offset slice and the
criticality ledger are not formalized here.

## Controls

- $`(q,c,D)=(2,1,3)`$: the return time is $`2`$, the accessible residues are
  $`0`$ and $`1`$, and residue $`2`$ satisfies $`F(2)=2`$, so it is a fixed
  residue that the orbit never visits.
- $`(q,c,D)=(2,1,7)`$: the return time is $`3`$ and the accessible residues are
  $`0,1,3`$; residues $`2,4,5,6`$ are inaccessible.
- $`(q,c,D)=(2,1,15)`$: the return time is $`4`$, so $`\gcd(q,D)=\gcd(c,D)=1`$
  does not imply full access.
- $`(q,c,D)=(3,1,2)`$: the return time is $`2=D`$, the case of full access.
- Multiplier $`q=D-1`$: the map is $`r\mapsto c-r\bmod D`$, so every offset
  $`c`$ not divisible by $`D`$ has return time $`2`$.
- At $`j=0`$ the orbit is $`0`$ and the criterion reads $`M\mid0`$, which holds
  for every modulus; the prime rows hold for every $`j\ge0`$, with both sides
  trivial at $`j=0`$, and the criterion is used at $`j\ge1`$.

## Formal dependencies

- `QCD.Repunit.001` provides the repunit sum and its recursion, product
  identity $`(q-1)G_j(q)=q^{j}-1`$, monotonicity and divisibility lemmas used
  in rows .2–.5.
- `Foundations.Main.StartHere` provides the iterate of a self-map and the block
  splitting used in rows .1 and .8.
- Mathlib supplies finite-set cardinality with its image operations
  (`Mathlib.Data.Finset.Card`), modular arithmetic (`Mathlib.Data.Nat.ModEq`),
  prime arithmetic (`Mathlib.Data.Nat.Prime.Basic`) and the finite-field power
  congruence used for the Fermat step in row .16 (`Mathlib.Data.ZMod.Basic`,
  `Mathlib.FieldTheory.Finite.Basic`).

## Go certificate

`go/ResidueAccess.go` recomputes the orbit, the access modulus and the least
return time with exact integer arithmetic and prints one counter per checked
instance:

| Slice | Checks |
|-------|--------|
| Closed form against the walked orbit, $`2\le q\le24`$, $`1\le c\le12`$, $`2\le D\le24`$, $`0\le j\le20`$ | 133308 |
| Return criterion against $`M\mid q^{j}-1`$, same rectangle, $`1\le j\le20`$ | 126960 |
| Least return time versus the least exponent with $`q^{m}\equiv1\pmod M`$ for coprime $`q,D`$, including $`m\le D`$ and the period test $`j\equiv0\pmod m`$ | 103467 |
| Prime full access for $`p\in\{2,3,5,7,11,13\}`$, $`q\le40`$, $`p\nmid c`$: $`m=p`$ and exhaustion of the residues | 1433 |
| Prime necessity for the same primes with $`q\not\equiv1\pmod p`$: $`m<p`$ and exactly $`p-m`$ unreached residues | 2044 |
| Worked examples, the trap residue modulo three and the multiplier $`D-1`$ slice | 88 |

The total is 367300 checks. The certificate checks rows .1–.5 and .9–.11 on
the swept instances, together with the prime statements .15–.16 and the worked
examples; the remaining rows are proved but not swept beyond those instances.
All residue arithmetic in the sweeps stays below $`2^{58}`$, the largest
product in a residue step being $`24\cdot23+12=564`$ and the largest in the
prime sweep $`40\cdot12+12=492`$; that bound is a property of the printed
ranges and is not enforced at run time. Exact repunits are computed with
`math/big` and exceed it. The sweeps are finite evidence about the printed
ranges, not a substitute for the theorems.

`go/ResidueAccess_test.go` recomputes the offsets with an independent `uint64`
walk and the modulus, the least return time and the exhaustion counts with
`math/big` routines written independently of the sweeps; it compares production
routines with those references, pins the six slice counts and the total, checks
the documented bounds and verifies that the orbit walk allocates nothing after
warm-up.

## Build and checks

- `make lean` builds this module together with the rest of the library.
- `make go GOFILE=QCD.ResidueAccess.001/go/ResidueAccess.go` runs the
  certificate.
- `CGO_ENABLED=0 go test -count=1 ./QCD.ResidueAccess.001/go` runs the tests.
- `make tex TEXFILE=QCD.ResidueAccess.001/tex/ResidueAccess.tex` builds the
  companion document.
