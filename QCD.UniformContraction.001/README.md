<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Uniform contraction outside a radius

Let $`T`$ be a self-map of the integers and let $`R`$ be a natural number. Write $`T^{k}`$ for the $`k`$-fold iterate. The absolute-value inequality $`|T(n)|\le |n|/2`$ is the same statement as $`2|T(n)|\le |n|`$.

## Statements

If $`2|T(n)|\le |n|`$ whenever $`|n|>R`$, then for every integer $`n`$ there is a $`k\le |n|`$ with $`|T^{k}(n)|\le R`$. This is UniformHalfEntry. The same hypothesis and the size bound $`|n|<2^{h}(R+1)`$ give an entry time $`k\le h`$. This is UniformHalfBudget. The identical induction on a natural-number map, with $`2T(n)\le n`$ whenever $`n>R`$, is NatHalfEntry.

Let $`a,d,b`$ be natural numbers with $`a<d`$, and set
```math
K=\frac{b}{d-a},\qquad H(x)=\frac{ax+b}{d},\qquad N_{0}=\lfloor K\rfloor.
```
The identity AffineMajorantIdentity is $`H(x)=K+(a/d)(x-K)`$. It implies AffineMajorantStrictDecrease: $`K<n`$ forces $`H(n)<n`$. It also implies AffineCoreBound: $`n\le N_{0}`$ forces $`H(n)<N_{0}+1`$. Thus a natural-number map with $`T(m)\le H(m)`$ for every $`m`$ sends $`\{0,1,\ldots,N_{0}\}`$ into itself, which is AffineCoreInvariant, and every orbit enters that segment in at most $`n`$ steps, which is AffineMajorantEntry.

The iterate is $`H^{h}(x)=(a/d)^{h}(x-K)+K`$, namely IterateMajorantFormula. Whenever
```math
d^{h}\bigl((N_{0}+1)-K\bigr)>a^{h}(x-K),
```
IterateMajorantBelowCore gives $`H^{h}(x)<N_{0}+1`$. Nonnegative slope makes $`H`$ and every iterate monotone. An integer orbit bounded pointwise by $`H`$ therefore stays below the corresponding majorant orbit.

If $`2a<d`$ and $`2b<n(d-2a)`$, then $`H(n)<n/2`$. Every integer $`n>2b`$ satisfies the second inequality because $`d-2a\ge 1`$. A natural-number map bounded by $`H`$ on that region therefore obeys $`2T(n)\le n`$ there, and NatHalfEntry puts every orbit into the radius $`2b`$.

## Reduction record

Original obligation: from a uniform bound $`|T(n)|\le |n|/2`$ outside a stated radius, conclude that every integer orbit enters the radius.

Replacement obligations: use the equivalent integer inequality $`2|T(n)|\le |n|`$, and prove entry by strong induction on $`|n|`$.

Recovery argument: for an integer value, $`2|T(n)|\le |n|`$ if and only if $`|T(n)|\le |n|/2`$. The inductive step returns an entry witness for $`T(n)`$, and one extra application of $`T`$ is an entry witness for $`n`$.

Difficulty decrease: outside the radius, $`|T(n)|<|n|`$. The induction measure is the absolute value, which is a natural number and strictly decreases at every unresolved step. The zero measure is already inside every radius.

Preservation conditions: the radius and the map remain arbitrary data subject only to the contraction hypothesis. The conclusion is entry into the radius, not a description of the orbit after entry. The step bound $`k\le |n|`$ is part of the proved statement.

Affine replacement: if $`a<d`$ and $`T(m)\le H(m)`$ for every natural number $`m`$, the fixed-point identity reduces entry to the same strict decrease, now measured by $`n`$ while $`n>N_{0}`$. The half-contraction radius $`2b`$ is available only under the stronger slope restriction $`2a<d`$; it is coarser than $`N_{0}`$ and is not a substitute for the floor argument when $`2a\ge d`$.

## What is not claimed

The contraction inequality is a hypothesis, not a theorem about the classical Collatz map or about any named residue-class map. The majorant bound is assumed at every natural number used by the induction. A state at which that bound fails is not given a forward description. No periodic classification inside the radius is proved. No statement is made about division traps, residue leakage, repunit divisors, or a comparison of the shape $`2\rho\le \mu\le 4\rho`$. A finite numerical check of one contracting family is evidence only for the integers on which it is evaluated.
