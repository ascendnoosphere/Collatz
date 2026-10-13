<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Coprime scaling and offset normalization

[Detailed proofs](tex/Scaling.tex) ·
[Formal proofs](lean/GeneralizedScaling.lean) ·
[Exact arithmetic](go/OffsetNormalization.go) ·
[Arithmetic tests](go/OffsetNormalization_test.go)

Let
```math
F_{q,c,d}(n)=
\begin{cases}
n/d,&d\mid n,\\ qn+c,&d\nmid n,
\end{cases}
\qquad q,c,d,n\in\mathbb Z,
\qquad |d|\ge2.
```
The signed divisor and the division-first guard are part of the map.

## QCD.Scaling.001.1 — coprime scaling

If $`\gcd(|h|,|d|)=1`$, then
```math
F_{q,hc,d}^{\,s}(hn)=hF_{q,c,d}^{\,s}(n)
```
for every $`s\in\mathbb N`$ and $`n\in\mathbb Z`$.
The equivalence
```math
d\mid hn\quad\Longleftrightarrow\quad d\mid n
```
ensures that the same raw branch is taken at every step. Since $`h\ne0`$,
scaling preserves all return times and therefore every primitive raw period.

Coprimality is necessary for this universal statement. For example,
```math
F_{3,2,2}(2)=1\ne8=2F_{3,1,2}(1).
```

## QCD.Scaling.001.2 — budgeted entry

Let $`A(t,n)`$ be the number of affine instructions among the first $`t`$
raw steps from $`n`$. If
```math
\gcd(|c|,|d|)=1,
\qquad c\mid q^r n,
```
then some $`t\in\mathbb N`$ satisfies
```math
c\mid F_{q,c,d}^{\,t}(n),
\qquad A(t,n)\le r.
```
The proof descends lexicographically in $`(r,|n|)`$. A division preserves
$`r`$ and strictly decreases $`|n|`$; an affine instruction decreases $`r`$.

## QCD.Scaling.001.3 — exact unit-offset tail

Assume
```math
\gcd(|c|,|d|)=1,
\qquad c\mid q^k.
```
For every integer seed $`n`$, there are $`t\in\mathbb N`$ and $`m\in\mathbb Z`$
such that
```math
F_{q,c,d}^{\,t}(n)=cm,
\qquad A(t,n)\le k,
```
and, for every $`s\in\mathbb N`$,
```math
F_{q,c,d}^{\,t+s}(n)=cF_{q,1,d}^{\,s}(m).
```
This is a full raw-clock identity after entry, not an accelerated or rational
substitution.

## QCD.Scaling.001.4 — capture equivalence

For any target $`T\subseteq\mathbb Z`$, all integer orbits of
$`F_{q,c,d}`$ meet $`T`$ if and only if every integer $`m`$ has an $`s`$ with
```math
cF_{q,1,d}^{\,s}(m)\in T.
```
No invariance of $`T`$ is required. Taking $`T=cS`$ gives the equivalent
unit-offset obligation that every orbit of $`F_{q,1,d}`$ meets $`S`$.

If additionally $`q\ge0`$, $`c>0`$, and $`d>0`$, positive states remain
positive. The entry state then has the form $`cm`$ with $`m>0`$, so the same
capture equivalence restricts to the positive state domain.
