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
Every seed $`n>1`$ outside $`\mathcal R_*`$ has a proved smaller-parent join.
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

Every seed $`n>1`$ outside $`\mathcal R_{**}`$ has a proved smaller parent
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

Every seed $`n>1`$ outside $`\mathcal R_{\dagger}`$ has a proved smaller-parent
join. Capture on $`\mathcal R_{\dagger}`$ would imply universal positive capture,
with the same logarithmic parent-depth bound. Neither that remaining capture
nor an exhaustive parent cover is established here.

## Direct descents in eight residual cylinders

Seven disjoint dyadic cylinders have the following uniform direct descents:

| source | shortcut word | descendant | raw ticks |
|---|---|---|---:|
| $`175+256t`$ | `11110100` | $`167+243t`$ | 13 |
| $`199+256t`$ | `11101010` | $`190+243t`$ | 13 |
| $`287+1024t`$ | `1111101000` | $`205+729t`$ | 16 |
| $`367+1024t`$ | `1111011000` | $`262+729t`$ | 16 |
| $`507+1024t`$ | `1101101100` | $`362+729t`$ | 16 |
| $`583+1024t`$ | `1110101100` | $`416+729t`$ | 16 |
| $`815+1024t`$ | `1111010100` | $`581+729t`$ | 16 |

Every row is legal for all $`t\ge0`$, and each descendant $`p`$ satisfies
$`24p\le23n<n`$. Their intersections with the previous residual all retain
exactly $`44`$ parameter classes modulo $`81`$. Thus, for their union
$`\mathcal C`$,

```math
d(\mathcal R_{\dagger}\cap\mathcal C)
 =\left(\frac2{256}+\frac5{1024}\right)\frac{44}{81}
 =\frac{143}{20736}.
```

The legal word $`11011010`$ supplies an eighth cylinder:

```math
T^8(123+256t)=118+243t<123+256t,
\qquad123(118+243t)\le118(123+256t).
```

Its five odd letters make the raw clock $`13`$. For this cylinder,

```math
123+256t\in\mathcal R_{\dagger}
\iff
 t\not\equiv2\pmod3,\quad
 t\not\equiv4\pmod9,\quad
 t\not\equiv10\pmod{81},\quad
 t\not\equiv30\pmod{32}.
```

Consequently,

```math
d(\mathcal R_{\dagger}\cap(123+256\mathbb N))
 =\frac1{256}\frac{44}{81}\frac{31}{32}
 =\frac{341}{165888}.
```

The seven source classes are disjoint from $`123\pmod{256}`$. Defining

```math
\mathcal R_{\mathrm D}=\mathcal R_{\dagger}
 \setminus\bigl(\mathcal C\cup(123+256\mathbb N)\bigr)
```

gives the exact density

```math
d(\mathcal R_{\mathrm D})=\frac{65659}{2654208}.
```

Every seed $`n>1`$ outside $`\mathcal R_{\mathrm D}`$ now has a positive smaller
parent with $`123p\le118n`$. Parent reduction reaches one or this residual
in at most $`\lceil\log n/\log(123/118)\rceil`$ reductions. Capture on
$`\mathcal R_{\mathrm D}`$ would imply universal positive capture; it is
not proved here.

## Twenty-four further certificates

A prefix-free family of twenty-one more dyadic cylinders has direct
descendants $`p`$ satisfying $`4p<3n`$. At depth ten the source residues
and base descendants are

```math
347\mapsto248,\qquad423\mapsto302,
```

with parameter slopes $`1024\mapsto729`$. At depth twelve they are

| source residue $`r`$ | base descendant $`p_0`$ |
|---:|---:|
| 2203 | 1177 |
| 3675 | 1963 |
| 2907 | 1553 |
| 1787 | 955 |
| 1019 | 545 |
| 3143 | 1679 |
| 3911 | 2089 |
| 1703 | 910 |
| 935 | 500 |
| 231 | 124 |
| 3119 | 1666 |
| 2351 | 1256 |
| 1647 | 880 |
| 879 | 470 |
| 2031 | 1085 |
| 2591 | 1384 |
| 1823 | 974 |
| 2975 | 1589 |
| 2239 | 1196 |

with slopes $`4096\mapsto2187`$. Thus every row means
$`T^h(r+2^ht)=p_0+3^kt`$, with $`(h,k)=(10,6)`$ or $`(12,7)`$.
The exact intersection of their union $`\mathcal A`$ with
$`\mathcal R_{\mathrm D}`$ has density $`1529/442368`$.

Two deeper cylinders and one smaller-parent join are

```math
T^{13}(2075+8192t)=1663+6561t,\qquad 6p\le5n.
```

```math
T^{59}(27+2^{59}t)=23+3^{37}t,\qquad 7p\le6n.
```

```math
T(111+2^{15}3^7t)=T^{12}(103+2^{26}t)
 =167+2^{14}3^8t,\qquad 123p\le118n.
```

Their raw clocks in the first two rows are $`21`$ and $`96`$. The three
exact new residual densities are respectively

```math
\frac{77}{1327104},\qquad
\frac{11}{11673330234144325632},\qquad
\frac1{71663616}.
```

All twenty-four source families are disjoint inside $`\mathcal R_{\mathrm D}`$.
After removing them, define $`\mathcal R_{\mathrm E}`$; exact subtraction gives

```math
d(\mathcal R_{\mathrm E})
 =\frac{6689147268412473047}{315179916321896792064}.
```

Every seed $`n>1`$ outside $`\mathcal R_{\mathrm E}`$ has an orbit-linked
parent $`p<n`$ with $`123p\le118n`$. Hence capture on $`\mathcal R_{\mathrm E}`$
would imply universal capture with the same logarithmic parent-depth bound.
Capture on this residual remains unproved.

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

## Bounded-depth obstruction in the persistent 27-cell

For $`n(t)=27+1024t`$, exact substitution in every earlier guard gives

```math
n(t)\in\mathcal R_{\mathrm D}
\iff
 t\not\equiv2\pmod3,
 t\not\equiv7\pmod9,
 t\not\equiv76\pmod{81},
 t\not\equiv42\pmod{64}.
```

Let $`\tau_L`$ be the unique residue modulo $`2^L`$ satisfying
$`183+6561\tau_L\equiv0\pmod{2^L}`$. For $`L\ge6`$,
$`\tau_L\equiv41\pmod{64}`$. The guarded set

```math
\mathcal E_L=
\{27+1024t:t\ge0,\ t\equiv\tau_L\pmod{2^L}\text{ and the three odd-modulus
conditions above hold}\}
```

is infinite and has density $`44/(81\cdot2^{L+10})`$. Its time-ten state is
$`182+6561t`$; the next $`L`$ transitions use the odd branch and increase.
For $`L\ge6`$, this set also misses all twenty-four new source families:
its source cannot lie in a depth-at-most-twelve direct cylinder, its parameter
is odd rather than in the deep $`27`$ subcylinder, and the remaining residue
checks exclude the $`2075`$ and $`111`$ families. Hence
$`\mathcal E_L\subset\mathcal R_{\mathrm E}`$. For every fixed depth $`H`$,
choosing $`L\ge\max\{6,H\}`$ leaves infinitely many new-residual seeds with
no descent through depth $`H`$.

The TeX proof also exhausts the five parents obtained by preserving the same
odd parameter $`v`$ and shortening this cell's second odd run. For any
fixed finite list of source and parent words, first choose $`L`$ at least
their maximum length. If a pair, even of initially different lengths, gave
an affine identity, unique factorization of its slopes would force equal
lengths and $`r_p-r_s=d>0`$. On $`\mathcal E_L`$, the legal source tail
begins $`01\,1^L`$, whereas every legal parent tail begins even, forcing
$`r_p\le r_s`$. Hence no finite dyadic cover of
the precise form stated in the TeX theorem, whose leaves use direct descent
from the source or a fixed affine collision from that tail with one of these
five parents, can exhaust the remaining portion of the $`27\pmod{1024}`$
cylinder in $`\mathcal R_{\mathrm E}`$. This is a method obstruction, not a divergent
positive orbit: the nested dyadic parameters converge to the 2-adic value
$`-183/6561`$, whose time-ten state is $`-1`$. Parents constructed after a
different prefix, parameter-dependent joins not fixed on a finite dyadic
cover, or a well-founded unbounded-depth recursion remain open.

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

The four Lean files prove the earlier displayed cylinder guards, identities,
and parent inequalities. For the twenty-four further certificates,
`ClassicalCoalescence.lean` proves every shortcut endpoint identity and parent
inequality. Its generic dyadic-lifting theorem derives each uniform identity
from a checked base trajectory and odd-input count; the displayed parity words
and raw clocks are checked by Go and proved in the TeX argument rather than
exposed as separate Lean conclusions. The files also prove the odd-run formula,
the terminal valuation and endpoint equation, and both
directions of terminal-prefix classification
with the endpoint exponent retained. They also prove the uniform second-burst
joins for both initial lengths, with no bound on the second length,
their original-source contraction, arithmetic membership recovery, and the
entire residual cylinders $`411+1536t`$ and $`615+3072t`$.
`PairedTails.lean` additionally proves the three legal tail relations, both
uniform paired joins, their original-source contractions and membership recovery,
and the two displayed multiple-of-three cylinder joins, endpoints and earlier
residual guards. Its joins also impose no upper bound on the second run.
The complete residual recovery, natural density, bounded-depth obstruction,
first-arrival and peak claims have written proofs; they are not declared as
Lean theorems in these files. The separate
[SwarmLemma.lean](../QCD.SwarmAttack.001/lean/SwarmLemma.lean) proves the
cylinder criterion and repeated-word divisibility criterion for all
natural seeds, words, and copy counts, including the empty word. Its proof
uses exact one-copy defect transport and cancellation of an odd multiplier
against a power of two. The maximal-copy valuation formula remains a written
corollary. The [retained uniform checker](../QCD.SwarmAttack.001/go/SwarmChecks_test.go)
checks all 31 direct cylinders and both legs of the smaller-parent join by
exact affine coefficients, independently of parameter sampling.

The Go companion checks cylinder parameters $`t=0,\ldots,10000`$,
all eight initial direct shortcut and raw clocks on that range, the seven complete
$`81`$-class residual periods, and all $`2592`$ classes in the eighth
cylinder's residual period. It also checks all twenty-one further direct
identities and raw clocks through $`t=10000`$, their complete $`1296`$-class
periods, both deep identities and the $`111`$ join through $`t=10000`$,
and the exact deep residual counts $`308/648`$ and $`44/81`$. The $`27`$
count independently evaluates every defining residual guard with exact big
integers. It checks parent rules for
$`2\le n\le100000`$ and both
guarded second-burst families through
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
