<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Positive squares in two dyadic equations

For a positive integer $`x`$ and natural numbers $`D,n`$, consider

```math
x^2+D=2^n.
```

A difference-of-squares identity settles every even exponent for
$`D=7,23`$. Explicit square brackets settle the remaining odd exponents
through $`n=32`$.

[Detailed proofs and square tables](tex/BeukersList.tex) ·
[Lean proofs](lean/BeukersList.lean) ·
[Exact finite checks](go/BeukersList.go)

## Complete even-exponent classification

For every natural number $`m`$ and every positive integer $`x`$,

```math
x^2+7=2^{2m}\quad\Longleftrightarrow\quad x=3\ \text{and}\ m=2.
```

There is no positive solution of $`x^2+23=2^{2m}`$.
The identity

```math
(2^m)^2-(2^m-1)^2=2^{m+1}-1
```

places $`2^{2m}-7`$ between consecutive squares for $`m\ge3`$, and
$`2^{2m}-23`$ between consecutive squares for $`m\ge4`$. The finitely many
smaller exponents are evaluated directly.

## All positive solutions through exponent 32

| Parameter | Positive solution pairs $`(x,n)`$, with $`n\le32`$ |
|---|---|
| $`D=7`$ | $`(1,3),(3,4),(5,5),(11,7),(181,15)`$ |
| $`D=23`$ | $`(3,5),(45,11)`$ |

The paper gives an integer-square bracket for each remaining odd exponent.
The Lean file proves that the positive-root enumeration is equivalent to the
original equation and computes both finite lists using proved square-root
bounds. These bounded statements do not classify odd exponents above 32.

## Two representations of every Mersenne parameter

For every integer $`k\ge4`$,

```math
1^2+(2^k-1)=2^k,
\qquad
(2^{k-1}-1)^2+(2^k-1)=2^{2k-2}.
```

Both roots are positive and distinct, and the exponents are distinct.
This is a uniform identity, not merely a finite enumeration or a
classification of every parameter admitting two representations.

## Build and run

From the repository root:

```sh
lake build BeukersList
CGO_ENABLED=0 go test ./QCD.BeukersList.001/go
make go GOFILE=QCD.BeukersList.001/go/BeukersList.go
make tex TEXFILE=QCD.BeukersList.001/tex/BeukersList.tex
```

The Go command checks 165 assertions: the seven displayed identities,
all exponents $`0\le n\le32`$, the Mersenne identities for $`4\le k\le32`$,
and deliberately incorrect predicates. Its finite checks are separate
from the uniform theorems proved in Lean and in the paper.
