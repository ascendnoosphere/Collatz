SPDX-License-Identifier: CC-BY-4.0

# Parent certified time

[Detailed proofs](tex/RecursiveClose.tex) ·
[Formal proofs](lean/RecursiveClose.lean) ·
[Exact arithmetic](go/RecursiveClose.go) ·
[Arithmetic tests](go/RecursiveClose_test.go)

Let $`T`$ be the classical shortcut on the natural numbers, including zero:
```math
T(x)=
  \begin{cases}
    x/2,&x\text{ even},\\     (3x+1)/2,&x\text{ odd}.
  \end{cases}
```
Iterates are $`T^{0}(x)=x`$ and $`T^{k+1}(x)=T(T^{k}(x))`$. For $`a,b,t\in\mathbb N`$,
```math
\tau(a,b,t)=
  \begin{cases}
    a+(t-b),&b\le t,\\     a+((b-t)\bmod 2),&b>t.
  \end{cases}
```

## Statements

The shortcut fixes $`0`$. It exchanges the terminal states:
```math
T(1)=2,\qquad T(2)=1.
```
Consequently, for every $`m\in\mathbb N`$,
```math
T^{m}(1)=
  \begin{cases}
    1,&m\text{ even},\\     2,&m\text{ odd}.
  \end{cases}
```
A positive input stays positive, every iterate of $`0`$ is $`0`$, and $`T^{n}(x)=1`$ forces $`x\ge 1`$. Iterates concatenate by
```math
T^{m+n}(x)=T^{m}(T^{n}(x)).
```

If $`T^{t}(p)=1`$ and $`T^{a}(n)=T^{b}(p)`$, then
```math
T^{\tau(a,b,t)}(n)=1.
```
When $`b\le t`$, the identity is the unused parent tail of length $`t-b`$. When $`b>t`$, the parent has entered the cycle $`1\leftrightarrow 2`$, and $`(b-t)\bmod 2`$ is the number of further steps from the join state back to $`1`$.

This time need not be least:
```math
\tau(2,0,0)=2,\qquad T^{2}(1)=1,\qquad T^{0}(1)=1.
```
The odd phase is sometimes necessary:
```math
\tau(0,1,0)=1,\qquad T^{1}(1)=2,\qquad T^{1}(2)=1.
```

## Reduction record

Original obligation: from a join $`T^{a}(n)=T^{b}(p)`$ and a time $`t`$ with $`T^{t}(p)=1`$, produce a time at which the shortcut orbit of $`n`$ equals $`1`$.

Replacement obligation: evaluate the two-case natural-number expression $`\tau(a,b,t)`$.

Recovery argument: if $`b\le t`$, concatenate the $`a`$ source steps with the $`t-b`$ remaining parent steps. If $`b>t`$, the same concatenation reduces the join state to $`T^{b-t}(1)`$, which TerminalPhase sends to $`1`$ in $`(b-t)\bmod 2`$ steps.

Difficulty decrease: after the join and the parent time are given, no further source tail is searched. The remaining data are a subtraction, when $`b\le t`$, or one remainder modulo $`2`$, when $`b>t`$.

Preservation conditions: the join equality, the hypothesis $`T^{t}(p)=1`$, and the shortcut on the natural numbers are retained. Positivity of a state that reaches $`1`$ is proved, not assumed as an extra restriction. Existence of $`p`$, minimality of $`\tau`$, and closure of an arbitrary chain of joins are not retained, because they are not part of the identity.

## What is not claimed

The identity does not assert that every positive integer has a parent, that a parent search finds a next node, or that every parent obligation closes. A chain that has already been produced may be replayed by this formula; the formula does not generate the chain. The certified time is not the first arrival at $`1`$ in general. No height bound for a repeated affine block is proved. No finite seed of the form $`15\cdot 2^{3a}-5`$, and no shortcut time attached to such a seed, is proved.

The finite grid
```math
1\le p\le 32,\qquad 0\le t,b\le 16,\qquad 0\le a\le 6,
```
retains rows with $`T^{t}(p)=1`$ and uses the source $`T^{b}(p)\cdot 2^{a}`$. Each such row contributes three integer comparisons: the doubling product is in range, $`a`$ halvings return the join, and $`\tau(a,b,t)`$ steps reach $`1`$. That grid illustrates the identity. It is not the identity, and it is not a contiguous verification range.

The following are not proved: the comparison $`2\rho\le\mu\le 4\rho`$; a lane decomposition of an affine family; a residue order; a uniform contraction; a repunit divisor law; a reverse search bound; a profile drop; a neutral discriminator; phase rigidity of a continuization; a finite family splitting; an excursion or cyclic gap; a terminal power; and a marginal repair.

## Finite certificate

The Go program prints the number of exact comparisons on the grid above. Its tests reject a predicate that is true of every pair, including the decoy clock that returns only $`a`$. A zero failure count under that predicate is not a certificate.
