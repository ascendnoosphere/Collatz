<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Raw-map 2-adic coding and positive-integer capture

Status: **REFORMULATION ONLY** for the exact capture criterion;
**REFUTED ROUTE** for coefficient-independent statistical transfer.
This report uses the raw map $`C(n)=n/2`$ on even inputs and $`C(n)=3n+1`$
on odd inputs. It does not use the shortcut clock of the other reports.
The positive capture target is unchanged by compressing each odd raw step
and its mandatory following halving into one shortcut tick.

## Source hypotheses

The homeomorphic conjugacy in
[DyadicTopology.tex](../../QCD.DyadicDynamics.001/tex/DyadicTopology.tex)
applies when $`q,c`$ are odd, hence to $`(q,c)=(3,1)`$. It identifies
$`C`$ on $`\mathbb Z_2`$ with the left shift on

```math
\Sigma=\{s\in\{0,1\}^{\mathbb N}:s_js_{j+1}=0\},\qquad
\Psi(x)_j=C^j(x)\bmod2,\qquad \Psi C=\sigma\Psi.
```

The integer dichotomy in
[DyadicDynamics.tex](../../QCD.DyadicDynamics.001/tex/DyadicDynamics.tex)
has the different hypothesis $`q+c`$ odd. It cannot be applied to
$`(3,1)`$, for which $`q+c=4`$.
The finite-prefix density transfer in
[DyadicStatistics.tex](../../QCD.DyadicDynamics.001/tex/DyadicStatistics.tex)
concerns unions of finite-depth cylinders, not arbitrary infinite-time events.

For a nonempty legal raw word $`w`$, let $`a`$ count its zeros, $`b`$ its
ones, and $`\delta`$ its final letter. Start with $`(a_j,b_j,M_j)=(0,0,0)`$
and scan from the left. A zero increments $`a_j`$ and leaves $`M_j`$
unchanged; a one increments $`b_j`$ and replaces $`M_j`$ by
$`3M_j+2^{a_j}`$. The resulting numerator satisfies

```math
C^h(x)=\frac{3^bx+M_w}{2^a},\qquad
C_w=\{x:x\equiv-M_w3^{-b}\pmod{2^{a+\delta}}\}.
```

These are the cylinder formulas of the cited conjugacy. With $`\mu`$
normalized Haar measure, $`\mu(C_w)=2^{-a-\delta}`$. For example, the
raw words $`1`$, $`01`$, and $`100`$ give respectively the classes
$`1\pmod2`$, $`2\pmod4`$, and $`1\pmod4`$. This identifies finite
parity data exactly; it does not decide eventual capture.

## The capture basin

Write $`w_1=(100)^\infty=\Psi(1)`$, since $`1,4,2`$ is the raw cycle.
Define

```math
B=\{s\in\Sigma:\exists j\ge0,\ \sigma^js=w_1\},\qquad
A=\Psi^{-1}(B)=\bigcup_{j\ge0}C^{-j}(\{1\}).
```

Each $`C^{-j}(\{1\})`$ is finite: a point has at most two raw
predecessors. Hence $`A`$ is countable, Haar-null, and a countable union
of closed singletons. It is dense. Indeed, any finite legal word $`u`$
can be followed by $`(100)^\infty`$ if it ends in zero, and by
$`0(100)^\infty`$ if it ends in one. The resulting sequence is legal,
belongs to $`B`$, and has prefix $`u`$. The empty prefix also extends.
The conjugacy transfers density from $`B`$ to $`A`$.

A countable set in these perfect spaces has empty interior and is meager.
The set $`A`$ is not closed: $`2^k\in A`$ tends 2-adically to
$`0\notin A`$. Its complement is dense because every nonempty cylinder
has positive Haar measure whereas $`A`$ is null. Thus no nonempty clopen
set is contained in $`A`$ or disjoint from it. Forward invariance follows
from the cycle; backward surjectivity follows from $`C(2x)=x`$.

The image $`\Psi(\mathbb N_{>0})`$ is also countable, dense, meager, and
null for the pushforward of Haar measure. It is shift-invariant, since
$`C`$ preserves positive integers and $`C(2n)=n`$ supplies a positive
predecessor. These shared properties do not establish inclusion in $`B`$.

## Exact pointwise criterion

For each positive integer $`n`$,

```math
n\text{ reaches }1
\quad\Longleftrightarrow\quad
\Psi(n)\in B
\quad\Longleftrightarrow\quad
\Psi(n)\text{ is eventually }(100)^\infty.
```

This follows directly from bijectivity and $`\Psi C=\sigma\Psi`$.
It is an equivalence, with no demonstrated reduction in proof difficulty.

Equivalently, let $`S`$ be the least subset of $`\mathbb N_{>0}`$
containing one and closed under $`y\mapsto2y`$ and, when $`y`$ is even
and $`y\equiv1\pmod3`$, under $`y\mapsto(y-1)/3`$.
Then $`S=A\cap\mathbb N_{>0}`$. Each inverse operation preserves
capture. Conversely, induction on the first hitting time recovers every
captured positive integer by its last inverse edge. This enumerates the
captured integers; it does not decide nonmembership or give a uniform
hitting-time bound.

## Limits of statistical transfer

At every finite depth, each cylinder meets both $`A`$ and its complement.
Thus a finite-depth inner approximation to $`A`$ by cylinder unions is
empty, and any such outer approximation is the whole space. Applying the
finite-prefix transfer theorem to these approximations gives only the
trivial bounds zero and one for an integer density, if that density exists.
A Haar-almost-everywhere statement also leaves every ordinary integer
exceptional, since the integers form a Haar-null set.

The finite-stage sets $`A_h=\bigcup_{j\le h}C^{-j}(\{1\})`$ are finite,
so each has ordinary density zero. Their increasing union need not have
density zero. For the raw comparison map with $`(q,c)=(-1,1)`$, every
positive integer reaches one. For $`|x|>2`$, two raw steps strictly
reduce $`|x|`$: the even-even case gives $`|x|/4`$, the even-odd case is
at most $`|x|/2+1<|x|`$, and the odd case gives $`|1-x|/2<|x|`$.
Hence every orbit enters $`\{-2,-1,0,1,2\}`$. The states $`-2,-1,2`$
reach one, and the only nonzero predecessor of zero is one, so a positive
orbit cannot reach zero without first reaching one.
Here the union has density one although every finite stage has density zero.
Consequently no exchange of hitting-time and density limits is available
from monotonicity alone.

The coefficient-independent golden-mean statistics cannot imply capture at
one for every odd parameter pair. At $`(q,c)=(1,3)`$, the positive cycle
$`3,6`$ never reaches one, although the same conjugacy hypotheses hold.
This counterexample rules out that uniform inference. It does not rule out
an arithmetic argument using the coefficient-dependent cylinder residues
for the specific pair $`(3,1)`$.

Nor do periodic-point counts alone locate ordinary integer cycles. For the
raw classical map, $`1/5,8/5,4/5,2/5`$ is a 2-adic four-cycle with no
ordinary integer point. The ambient zeta function counts it alongside
integer periodic points. Denominator divisibility and signs remain separate
arithmetic obligations.

The remaining target is exactly $`\mathbb N_{>0}\subseteq A`$, or
$`S=\mathbb N_{>0}`$. No bound or integer-point theorem proving that
inclusion is supplied by this report.
