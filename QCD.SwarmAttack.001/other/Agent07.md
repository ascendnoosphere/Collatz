<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Finite parity data and uniform descent

Status: **REFUTED ROUTE** for a fixed-precision cover by uniform direct
descents. The positive capture target is not resolved. This obstruction
allows smaller-parent joins, non-clopen covers, and unbounded recursion.

Use the shortcut $`T(n)=n/2`$ for even inputs and $`T(n)=(3n+1)/2`$ for
odd inputs. The [ClassicalCoalescence reduction](../../QCD.ClassicalCoalescence.001/README.md)
puts every least positive counterexample in its residual
$`\mathcal R_{\mathrm E}`$ by supplying a positive smaller parent outside it.

## Cylinders and strict descent

For a binary word $`w`$ of length $`h`$ with $`r`$ ones, write
$`F_w(n)=(3^rn+B_w)/2^h`$. Starting with $`B_0=0`$, appending the
letter $`\varepsilon_j`$ gives
$`B_{j+1}=3^{\varepsilon_j}B_j+\varepsilon_j2^j`$.

The word is legal exactly on the cylinder

```math
C(w)=\{n:n\equiv-B_w3^{-r}\pmod{2^h}\}.
```

For the empty word this is the whole domain. For the induction step, the
prefix value on $`a+2^ht`$ is $`F_w(a)+3^rt`$. Its parity selects exactly
one lift modulo $`2^{h+1}`$. The corresponding next affine numerator is
divisible by its denominator exactly on that lift. This proves legality
as well as integrality. It also proves that length-$`h`$ itineraries are
in bijection with the classes modulo $`2^h`$. The same criterion is proved
in [SwarmLemma.lean](../lean/SwarmLemma.lean).

Represent a class modulo $`2^k`$ by $`0\le a<2^k`$, and put
$`m_k(a)=a`$ when $`a>0`$, $`m_k(0)=2^k`$. A word is legal on the whole
class only if $`h\le k`$, since its legal set is one class modulo $`2^h`$.
When legal, it descends at every positive member exactly when

```math
3^r<2^h,\qquad B_w<(2^h-3^r)m_k(a).
```

Indeed, $`F_w(n)-n=((3^r-2^h)n+B_w)/2^h`$. A nonnegative slope cannot
be strictly negative because $`B_w\ge0`$. A negative slope has its largest
value at the least positive member. This proves both directions, including
the class represented by zero. It suffices to test the first $`k`$ itinerary
prefixes; no other word can be legal on that class.

Let $`U_k`$ be the classes with no such descent. A covered class has both
lifts covered at the next precision: the word stays legal and the least
positive representative cannot decrease. Thus
$`U_{k+1}\subseteq\operatorname{lift}(U_k)`$.

## A comparison graph is not an orbit quotient

One can record an edge $`a\to b`$ whenever a word supplies uniform descent
on the class of $`a`$ and
$`b\equiv F_w(m_k(a))\pmod{2^k}`$. Then

```math
m_k(b)\le F_w(m_k(a))<m_k(a).
```

This representative-based comparison graph is acyclic, with the explicit
rank $`m_k`$. It has out-degree zero exactly on $`U_k`$.
It is not a deterministic quotient of the actual orbit: for $`h>0`$,

```math
F_w(a+2^kt)-F_w(a)=3^r2^{k-h}t,
```

which need not vanish modulo $`2^k`$. In particular the even class at
precision $`k`$ has images differing by $`2^{k-1}`$ after one step.
Using $`F_w(a)`$ instead of $`F_w(m_k(a))`$ for the edge would also give
a spurious self-loop at the zero class. The earlier graph description did
not account for these two issues; the comparison graph above does.

## A permanently uncovered lineage

The ten-letter itinerary $`1101111101`$ gives

```math
T^{10}(27+1024t)=182+6561t.
```

At $`t^*=-183/6561\in\mathbb Z_2`$, its source is
$`n^*=-3415/2187`$ and its endpoint is $`-1`$, the odd shortcut fixed point.
Thus $`n^*`$ has that prefix followed by all ones. Its prefix one-counts
through time ten are $`1,2,2,3,4,5,6,7,7,8`$, so $`3^{r_h}>2^h`$ at
those times. For $`h\ge10`$, $`r_h=h-2`$ and the same inequality persists,
since it is already strict at ten and each extra letter multiplies the
ratio by $`3/2`$.

Every word legal on a class containing $`n^*`$ is one of these prefixes.
The descent criterion therefore fails on every such class, regardless of
its precision or the proposed word length. Hence
$`n^*\bmod2^k\in U_k`$ for every $`k\ge1`$.

For connection to the residual, let $`\tau_L`$ be the unique solution of
$`183+6561\tau_L\equiv0\pmod{2^L}`$, and set

```math
\mathcal E_L=\{27+1024t:t\ge0,\ t\equiv\tau_L\pmod{2^L},
\ t\not\equiv2\pmod3,\ t\not\equiv7\pmod9,\ t\not\equiv76\pmod{81}\}.
```

The residual-recovery calculation in the ClassicalCoalescence article proves
$`\mathcal E_L\subseteq\mathcal R_{\mathrm E}`$ for $`L\ge6`$.
The three exclusions discard 27, 9, and 1 disjoint classes modulo 81,
leaving 44. Since $`2^L`$ and 81 are coprime, each of those classes is
compatible with $`\tau_L`$, so $`\mathcal E_L`$ is infinite. Its members
are congruent to $`n^*`$ modulo $`2^{10+L}`$ by the displayed affine identity.

For every $`k\ge16`$, the class $`n^*\bmod2^k`$ consequently meets the
residual but has no uniform descent. No assignment of ranks to the comparison
graph can repair that absence of an outgoing edge. A finite cover by dyadic
uniform-descent cylinders would refine to one common precision, where the
same witness contradicts coverage. The
[mixed-radix argument](Agent10.md) treats arbitrary odd factors as well.
These are obstructions to the stated covers, not positive divergent orbits:
the limit point $`n^*`$ is not a positive ordinary integer.

## What the inverse limit retains

Put

```math
S=\{x\in\mathbb Z_2:x\bmod2^k\in U_k\text{ for every }k\ge1\}.
```

This is a nonempty compact set, since it is an intersection of nested clopen
sets and contains $`n^*`$. Its positive integer points satisfy the exact identity

```math
S\cap\mathbb N_{>0}
=\{n\ge1:T^h(n)\ge n\text{ for every }h\ge1\}.
```

If a class of $`n`$ is covered, its word already gives descent at $`n`$.
Conversely, suppose $`T^h(n)<n`$. The slope of that word must be less than
one, because its offset is nonnegative. Choose $`k\ge h`$ with $`2^k>n`$.
Then $`m_k(n)=n`$, the word is legal on the class, and its strict descent
at the least positive representative makes it a uniform descent there.
Thus $`n\notin S`$.

It follows by strong induction that $`S\cap\mathbb N_{>0}=\{1\}`$ is
equivalent to positive capture. Conversely, capture gives a smaller iterate
for every $`n>1`$, whereas the orbit $`1,2,1,\ldots`$ never goes below one.
The inverse-limit integer-point problem therefore retains the original
obligation; it is not a certified simplification.

## Historical computations

The original report recorded complete class enumeration through $`k=22`$,
uncovered-tree expansion through $`k=28`$, and residual checks for
$`6\le L\le16`$ in `/tmp/opencode/Agent07/main.go`. The program is not
retained, so its tables are not supplied as reproducible certificates.
The cylinder, comparison, and obstruction arguments above do not use those
tables. An adaptive smaller-parent construction or an independent theorem
excluding positive integers from $`S\setminus\{1\}`$ remains unproved.
