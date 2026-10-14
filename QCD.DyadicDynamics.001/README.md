<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Dyadic integer dynamics and the 2-adic raw clock

Use the division-first map

```math
T_{q,c}(n)=\begin{cases}n/2,&2\mid n,\\qn+c,&2\nmid n.\end{cases}
```

The integer results use $`q,c,n\in\mathbb Z`$. The compact dynamical
results use $`q,c,n\in\mathbb Z_2`$ and 2-adic convergence. These
conclusions refer to different absolute values and are kept separate.

[Signed integer proof](tex/DyadicDynamics.tex) ·
[2-adic topology and measure proof](tex/DyadicTopology.tex) ·
[Lean companion](lean/DyadicDynamics.lean) ·
[Exact finite checks](go/DyadicDynamics.go)

## Complete opposite-parity integer classification

Suppose $`q+c`$ is odd and $`|q|\ge2`$. Every nonzero seed is
$`n=2^k u`$ with $`u`$ odd. The first $`k`$ raw ticks are divisions,
and the odd branch is invariant thereafter. Its exact shifted coordinate is

```math
(q-1)T^{k+j}(n)+c=q^j((q-1)u+c).
```

- If $`(q-1)u+c=0`$, the tail is the fixed point $`u`$.
- Otherwise the entire raw orbit escapes in magnitude, with

```math
\lim_{j\to\infty}\frac{|T^{k+j}(n)|}{|q|^j}
=\left|u+\frac{c}{q-1}\right|>0.
```

The only possible nonzero periodic point is the odd integer
$`u_*=-c/(q-1)`$. Its basin is exactly $`\{2^k u_*:k\ge0\}`$.
The basin of zero is just zero. A negative multiplier gives eventual
sign alternation on every escaping tail.

This proves all-positive escape for even $`q\ge2`$ and positive odd $`c`$,
and for $`q=3`$ with nonnegative even $`c`$. With offset one and even
$`|q|\ge2`$, the only nonzero exceptions are $`-2^k`$ when $`q=2`$;
they reach $`-1`$. All other even such multipliers have full signed escape.

Eventual periodicity and signed target reachability are decidable throughout
this opposite-parity expanding family, in polynomial binary bit time.
After checking the finite halving prefix, target reachability reduces to
$`(q-1)m+c=q^j((q-1)u+c)`$. Repeated exact division of the target coordinate
by $`q`$ checks every possible exponent while strictly decreasing its magnitude.
The linked integer paper proves recovery of the legal raw state and an
$`O(L^3)`$ schoolbook bit bound, where $`L`$ is total binary input length.

The Lean theorems `DyadicDecomposition`, `DivisionPrefix`, `TailCertificate`,
`TailEscape`, `TailFixed` and `SeedOutcome` formalize the signed dichotomy
and its full-sequence recovery. `TailPeriodicOnlyFixed` certifies that
an expanding odd tail cannot have a nonfixed period.

## Three small multipliers and primitive excursions

For $`q=c=1`$, the first-division return is
$`H(n)=\lceil n/2\rceil`$ on positive integers. Thus

```math
H^h(n)=\lceil n/2^h\rceil.
```

Every positive seed reaches one in at most $`2\lceil\log_2 n\rceil`$
raw ticks. Its only positive primitive cycle is $`1,2`$.
Negative seeds reach zero. With $`q=0,c=1`$, every nonzero signed seed
reaches the fixed point one. With $`q=-1,c=1`$, every signed seed reaches
zero; every nonzero seed visits one first.

For $`q=2^k-1,c=1,k\ge1`$,

```math
1\longmapsto2^k\longmapsto2^{k-1}\longmapsto\cdots\longmapsto2\longmapsto1
```

is a primitive raw cycle of length $`k+1`$. The Lean companion proves
positive unit-multiplier capture and every phase, closure, and primitive
period of the Mersenne excursion. The logarithmic capture bound and the
constant/reflection classification have written proofs in the linked paper.
The Mersenne result specifies the cycle through one, not all odd-multiplier cycles.

## Golden-mean coding on the 2-adic integers

For odd $`q,c\in\mathbb Z_2`$, parity itineraries give a constructive
homeomorphic conjugacy to

```math
\Sigma=\{s\in\{0,1\}^{\mathbb N}:s_js_{j+1}=0\text{ for every }j\}.
```

An odd tick must be followed by an even tick. For a legal length-$`h`$ word
$`w`$ with $`a`$ zeros and final-letter indicator $`\delta`$, its source
cylinder is one class modulo $`2^{a+\delta}`$ and has Haar measure
$`2^{-a-\delta}`$. The cylinders shrink and reconstruct a unique 2-adic point.

Writing $`\varphi=(1+\sqrt5)/2`$, the raw topological entropy is
$`\log\varphi`$, and

```math
\#\operatorname{Fix}(T^h)=\operatorname{tr}(A^h),\qquad
A=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
\zeta_T(z)=\frac1{1-z-z^2}.
```

These are **2-adic** periodic-point counts and the corresponding formal
Artin–Mazur zeta function, not counts of ordinary integer cycles.

Let $`\mu`$ be normalized Haar probability. A raw invariant mixing
probability has density $`4/3`$ on even states and $`2/3`$ on odd states.
Its itinerary law has

```math
\pi=(2/3,1/3),\qquad
P=\begin{pmatrix}1/2&1/2\\1&0\end{pmatrix},\qquad
P^r=\Pi+(-1/2)^r(I-\Pi),
```

where $`\Pi`$ has both rows equal to $`\pi`$. The parity-block entropy
rate is $`(2/3)\log2`$. Every invariant probability corresponds to a
shift-invariant probability on $`\Sigma`$. The unique maximal-entropy
probability instead has transition probabilities $`\varphi^{-1}`$ and
$`\varphi^{-2}`$ in its even row and deterministic odd-to-even transition.
Its entropy is $`\log\varphi`$.

The first-division map $`H(n)=n/2`$ on even states and $`H(n)=(qn+c)/2`$
on odd states has the **full binary shift** coding and preserves Haar.
One $`H`$ tick takes one or two raw ticks. The two entropy and measure
laws therefore refer to different maps and clocks.

For even $`q\in\mathbb Z_2`$ and odd $`c`$, every nonzero 2-adic seed
converges to $`a=-c/(q-1)`$, whereas zero is fixed. All invariant
probabilities are exactly
$`\lambda\delta_0+(1-\lambda)\delta_a`$, $`0\le\lambda\le1`$.
The topological and all invariant metric entropies are zero. Its only
periodic points are these two fixed points, so its 2-adic Artin–Mazur zeta
function is $`(1-z)^{-2}`$.

The 2-adic conjugacies, invariant measures, mixing, entropy, and zeta
statements have detailed written proofs in `tex/DyadicTopology.tex`;
they are not Lean declarations. The Go tests check the finite cylinder
identities on odd $`q,c\in[-7,7]`$ through depth twelve, signed affine
certificates on a declared grid, and exact Mersenne phases through exponent
256. These finite checks do not replace the infinite proofs.
