<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Classical parent joins and terminal words

This topic uses the positive-integer shortcut

```math
T(n)=\begin{cases}n/2,&2\mid n,\\(3n+1)/2,&2\nmid n.\end{cases}
```

A legal word of length $`h`$ with $`r`$ odd letters takes $`h+r`$
classical raw ticks. A **smaller-parent join** consists of positive
$`p<n`$ and times $`b,c\ge0`$ with $`T^b(n)=T^c(p)`$. Capture of the
parent recovers capture of the source, even if their meeting point is
above the source. Strict decrease of the parent label permits strong induction.

[Detailed proofs](tex/ClassicalCoalescence.tex) ·
[Formal cylinder joins](lean/ClassicalCoalescence.lean) ·
[Formal terminal classification](lean/TerminalConverse.lean) ·
[Exact finite checks](go/ClassicalCoalescence.go)

## A smaller residual obligation

For odd $`n`$, write $`n=2^a u-1`$ with
$`a=v_2(n+1)\ge1`$ and $`u>0`$ odd. Define

```math
\mathcal R=\{2^a u-1:a\ge2,\ u>0\text{ odd},\ 3\nmid u,
                         \ 3^a u\equiv3\pmod4\}.
```

Four ordered rules give a positive smaller parent outside $`\mathcal R`$:

| Guard | Parent | Shortcut join |
|---|---|---|
| $`n`$ even | $`n/2`$ | $`T(n)=p`$ |
| $`n\equiv1\pmod4`$, $`n>1`$ | $`(3n+1)/4`$ | $`T^2(n)=p`$ |
| $`n\equiv2\pmod3`$ | $`(2n-1)/3`$ | $`n=T(p)`$ |
| $`a\ge2`$, $`3^a u\equiv1\pmod4`$ | $`(n-1)/2`$ | $`T^{a+2}(n)=T^{a+1}(p)`$ |

Each parent satisfies $`5p\le4n`$. The residual has natural density $`1/12`$.
Three further guarded words remove explicit portions of it:

```math
\begin{aligned}
T^3(3+8t)&=4+9t &&\text{parent word }110,\\ T^5(11+32t)&=10+27t &&\text{source word }11010,\\ T^6(7+64t)&=10+81t &&\text{parent word }111010.
\end{aligned}
```

Here $`t\ge0`$. In the second identity, membership of the source in
$`\mathcal R`$ excludes $`t=0`$. All applicable parents obey $`9p\le8n`$.
Thus the remaining obligation is capture on

```math
\mathcal R_*=
\{n\in\mathcal R:
 n\not\equiv4\pmod9,\ n\not\equiv11\pmod{32},\ n\not\equiv10\pmod{81}\}.
```

It has natural density $`11/216`$. The density calculation retains the
valuation tail: seeds with $`a\ge A`$ lie in one class modulo $`2^A`$.
Every seed outside $`\mathcal R_*`$ has a proved smaller-parent join.
Repeated parent reductions terminate at one or in $`\mathcal R_*`$ in at
most $`\log n/\log(9/8)`$ reductions. This bounds **parent depth**, not
forward stopping time. Capture on $`\mathcal R_*`$ implies universal
positive capture; capture on that residual is not established here.

For example, $`T^3(27+1024t)=31+1152t`$ supplies smaller parents for an
entire residual cylinder, and $`T^6(71)=91`$ covers another residual seed.
The separate identity

```math
T^6(79+128t)=T(67+108t)=101+162t
```

has a smaller parent despite no source descent in its first six shortcut ticks.
Its source lies outside $`\mathcal R`$; it illustrates the join mechanism,
not an additional residual density gain.

## Exact repetition budget

For any nonempty binary word $`w`$ of length $`h`$, compose its rational
branches as $`F_w(n)=(Pn+B)/Q`$, where $`P=3^{r(w)}`$ and $`Q=2^h`$.
Then

```math
w^k\text{ is legal at }n
\quad\Longleftrightarrow\quad
Q^k\mid (P-Q)n+B.
```

When the displacement is nonzero, the exact maximum number of complete
initial copies is $`\lfloor v_2(\lvert(P-Q)n+B\rvert)/h\rfloor`$.
For $`w=110`$ this is $`\lfloor v_2(n+5)/3\rfloor`$.
An expanding fixed word cannot repeat forever at a positive seed.
Switching between different words is not controlled by this fixed-word budget.

## Terminal-prefix equivalence

Fix $`a\ge2`$ and $`u>0`$ odd. The legal prefix $`1^a01`$ at
$`n=2^a u-1`$ ends at a power of two exactly when

```math
u=\frac{2^{3^a t}+1}{3^{a+1}}
\quad\text{for some positive odd }t.
```

For $`L=3^a t`$, the endpoint is $`2^{L-2}`$, the first arrival at one
is at shortcut time $`a+L`$, and the unique peak is $`(2^L-2)/3`$ at
time $`a`$. The valuation identity
$`v_3(2^L+1)=1+v_3(L)`$ for odd positive $`L`$ proves the converse as
well as the integrality required for construction.

## Formal and computational scope

The two Lean files prove the displayed cylinder identities, their guards
and parent inequalities, the odd-run formula, the terminal valuation and
endpoint equation, and both directions of terminal-prefix classification
with the endpoint exponent retained. The complete residual recovery,
natural density, general repetition budget, first-arrival and peak claims
have written proofs; they are not declared as Lean theorems in these files.

The Go companion checks cylinder parameters $`t=0,\ldots,10000`$,
parent rules for $`2\le n\le100000`$, all binary words of lengths one
through eight at seeds one through 256 with zero through three copies,
support windows through twelve with at most three crossings, all 35
five-return exponent-eight compositions, and nine terminal constructions
using exact big integers. These checks do not replace the uniform proofs.
The crossing theorem is in
[Three-crossing exclusion](../QCD.NoCrossing.001/README.md#three-crossing-extension),
and the short-cycle classification is in
[Classical closures with at most five odd states](../QCD.ThreeAffineClosure.001/README.md#classical-closures-with-at-most-five-odd-states).
