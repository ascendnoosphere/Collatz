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
[Formal second-burst joins](lean/SecondBurst.lean) ·
[Formal paired-tail joins](lean/PairedTails.lean) ·
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
These seven rules leave the intermediate residual

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

## Uniform second-burst joins

Two further rules have arbitrarily long clocks. For $`a\in\{2,3\}`$,
let $`\mathcal S_a`$ contain the positive sources $`n=2^a u-1`$ satisfying

```math
u>0\text{ odd},\quad b\ge1,\quad v>0\text{ odd},\quad
3^a u+1=2^{b+1}v,\quad 3^b v\equiv1\pmod4.
```

The odd factor $`v`$ makes $`b`$ unique. The legal words
$`1^a01^b00`$ and $`1^{b-1}01`$ give the common parent certificate

```math
p=2^{b-1}v-1=\frac{3^a u-3}{4},\qquad
T^{a+b+3}(n)=T^{b+1}(p),\qquad 0<p<n,\qquad 7p\le6n.
```

For $`a=2`$, the sharper relation is $`16p+3=9n`$;
for $`a=3`$, it is $`32p=27n+3`$.
The case $`b=1`$ has an empty initial odd run on the parent side
and is included. Both clocks are shortcut clocks. Their common endpoint is
$`(3^b v-1)/4`$; it need not be below the source.

Two whole residual multiple-of-three cylinders have

```math
\begin{aligned}
T^9(411+1536t)&=T^5(231+864t)=587+2187t,\\ T^{10}(615+3072t)&=T^5(519+2592t)=1316+6561t
\qquad(t\ge0).
\end{aligned}
```

At $`t=0`$, every positive source tick through each join exceeds its
original source, while the corresponding parent is smaller. These are
parent certificates before any source descent.

For fixed $`a,b`$, the guard selects one source class modulo
$`2^{a+b+3}`$. The tail $`b\ge B`$ lies in one class modulo
$`2^{a+B+1}`$, which justifies the infinite sums.
The $`a=2,b=1`$ class is already removed by the earlier exclusion
$`n\equiv11\pmod{32}`$. The remaining $`a=2`$ classes have
$`b\ge2`$, while the $`a=3`$ family includes every $`b\ge1`$.
Each of these two eligible families has density $`1/64`$ before
the odd-modulus restrictions. Consequently, for each $`a=2,3`$,

```math
d(\mathcal R_*\cap\mathcal S_a)
=\left(\frac23-\frac19-\frac1{81}\right)\frac1{64}
=\frac{11}{1296}.
```

This is half of each $`a=2`$ or $`a=3`$ part of
$`\mathcal R_*`$. The two removals are disjoint because their
sources have different valuations of $`n+1`$. This gives the residual

```math
\mathcal R_{**}=\mathcal R_*\setminus(\mathcal S_2\cup\mathcal S_3),\qquad
d(\mathcal R_{**})=\frac{11}{324},\qquad
d(\mathcal R_{**}\cap3\mathbb Z)=\frac1{48}.
```

Every positive seed outside $`\mathcal R_{**}`$ has a proved smaller parent
with $`9p\le8n`$. Parent reduction terminates at one or in this set,
with the same $`\log n/\log(9/8)`$ depth bound. Join recovery and strong
induction show that capture of every member of $`\mathcal R_{**}`$ would
imply universal positive capture. Capture on this residual remains
unproved; its smaller density is not a capture theorem.

## Paired eight-letter tails

Equal-length tails can compensate for shortening the parent's initial odd run.
For $`F_w(x)=(3^{r(w)}x+B_w)/2^h`$, write $`C_w=B_w-3^{r(w)}`$. Then

```math
F_w(3^b v-1)=\frac{3^{b+r(w)}v+C_w}{2^h}.
```

Three chronological words of length eight share $`C_w=125`$:

| Word | Rational map | Legal input modulo $`256`$ |
|---|---|---|
| $`00000001`$ | $`(3x+128)/256`$ | $`128`$ |
| $`01000001`$ | $`(9x+134)/256`$ | $`42`$ |
| $`01011100`$ | $`(81x+206)/256`$ | $`146`$ |

The exact input classes prove all intermediate guards, not just matching endpoints.
Let $`n=2^a u-1`$ and $`3^a u+1=2^{b+1}v`$, with $`u,v>0`$ odd.
Define $`\mathcal H_a`$ by $`a\in\{4,5,6\}`$, $`b\ge3`$,
and $`3^b v\equiv129\pmod{256}`$. Every such source has

```math
p=2^{b-3}v-1=\frac{3^a u-15}{16},\qquad
T^{a+b+9}(n)=T^{b+5}(p)=\frac{3^{b+1}v+125}{256},\qquad
0<p<n,\qquad1024p\le729n.
```

The source and parent tails are $`00000001`$ and $`01011100`$.
For the other family $`\mathcal J_a`$, take $`a\in\{2,3,4\}`$,
$`b\ge2`$, and $`3^b v\equiv43\pmod{256}`$. It gives

```math
p=2^{b-2}v-1=\frac{3^a u-7}{8},\qquad
T^{a+b+9}(n)=T^{b+6}(p)=\frac{3^{b+2}v+125}{256},\qquad
0<p<n,\qquad128p\le81n.
```

Here the source tail is $`01000001`$, and the parent tail is unchanged.
This family reaches the opposite terminal residue, $`3^b v\equiv3\pmod4`$.
There is no upper bound on $`b`$ in either family; both empty parent runs
($`b=3`$ and $`b=2`$, respectively) are included.
All comparisons use the original source $`n`$. Both bounds preserve $`9p\le8n`$.

For example, two entire cylinders inside $`\mathcal R_{**}\cap3\mathbb Z`$ satisfy

```math
\begin{aligned}
T^{16}(137199+5308416t)&=T^8(43410+1679616t)=13736+531441t,\\ T^{13}(7803+663552t)&=T^8(2194+186624t)=695+59049t
\qquad(t\ge0).
\end{aligned}
```

Put $`\mathcal H=\bigcup_{a=4}^6\mathcal H_a`$ and
$`\mathcal J=\bigcup_{a=2}^4\mathcal J_a`$. They are disjoint and do not meet
the earlier $`\mathcal S_2,\mathcal S_3`$ removals. For fixed $`a,b`$,
each guard specifies one class modulo $`2^{a+b+9}`$.
The tail $`b\ge B`$ has upper density at most $`2^{-(a+B+1)}`$,
so the infinite sums are justified. Before the odd-modulus restrictions,

```math
d(\mathcal H)=\frac7{131072},\qquad d(\mathcal J)=\frac7{16384}.
```

The CRT factor $`2/3-1/9-1/81=44/81`$ gives

```math
d(\mathcal R_{**}\cap\mathcal H)=\frac{77}{2654208},\qquad
d(\mathcal R_{**}\cap\mathcal J)=\frac{77}{331776}.
```

Thus the new residual and its densities are

```math
\mathcal R_{\dagger}=\mathcal R_{**}\setminus(\mathcal H\cup\mathcal J),\qquad
d(\mathcal R_{\dagger})=\frac{89419}{2654208},\qquad
d(\mathcal R_{\dagger}\cap3\mathbb Z)=\frac{8129}{393216}.
```

Every positive seed outside $`\mathcal R_{\dagger}`$ has a proved smaller-parent
join. Capture on $`\mathcal R_{\dagger}`$ would imply universal positive capture,
with the same logarithmic parent-depth bound. Neither that remaining capture
nor an exhaustive parent cover is established here.

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

The four Lean files prove the displayed cylinder identities, their guards
and parent inequalities, the odd-run formula, the terminal valuation and
endpoint equation, and both directions of terminal-prefix classification
with the endpoint exponent retained. They also prove the uniform second-burst
joins for both initial lengths, with no bound on the second length,
their original-source contraction, arithmetic membership recovery, and the
entire residual cylinders $`411+1536t`$ and $`615+3072t`$.
`PairedTails.lean` additionally proves the three legal tail relations, both
uniform paired joins, their original-source contractions and membership recovery,
and the two displayed multiple-of-three cylinder joins, endpoints and earlier
residual guards. Its joins also impose no upper bound on the second run.
The complete residual recovery,
natural density, general repetition budget, first-arrival and peak claims
have written proofs; they are not declared as Lean theorems in these files.

The Go companion checks cylinder parameters $`t=0,\ldots,10000`$,
parent rules for $`2\le n\le100000`$, both guarded second-burst families through
$`n=1000000`$ (46,875 sources, including 16,974 previously residual seeds),
all six paired-tail rank classes through that same source bound
(484 guarded sources, including 261 new residual removals and 163 multiples of three),
three eight-letter tail cylinders on every input $`0\le x<65536`$,
all binary words of lengths one
through eight at seeds one through 256 with zero through three copies,
support windows through twelve with at most three crossings, all 35
five-return exponent-eight compositions, and nine terminal constructions
using exact big integers. These checks do not replace the uniform proofs.
The crossing theorem is in
[Three-crossing exclusion](../QCD.NoCrossing.001/README.md#three-crossing-extension),
and the short-cycle classification is in
[Classical closures with at most five odd states](../QCD.ThreeAffineClosure.001/README.md#classical-closures-with-at-most-five-odd-states).
