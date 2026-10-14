<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Residue cylinders, drift and nonunit escape

For positive integer seeds, use the division-first raw rule

```math
T(n)=\begin{cases}n/D,&D\mid n,\\qn+c,&D\nmid n.\end{cases}
```

The unit-multiplier theorems below assume
$`q\ge2,c\ge1,D\ge2,\gcd(q,D)=1`$.
Let $`m`$ be the least positive zero-return time of the permutation
$`F(r)=qr+c\bmod D`$. Then $`1\le m\le D`$.
The prime-square theorem has a different, explicitly nonunit hypothesis.

[Strict-leakage proof](tex/ResidueLeakage.tex) ·
[Full-cycle drift proof](tex/ResidueBoundary.tex) ·
[Prime-square proof](tex/NonunitResidues.tex) ·
[Exact finite computation](go/ResidueCylinders.go)

## Strict leakage

For every depth $`h`$, seeds with at least $`h`$ **actual raw divisions**
occupy exactly $`m^h`$ classes modulo $`D^h`$.
A successful prefix with endpoint $`E`$ and numerator multiplier $`P`$
satisfies

```math
H^h(n+D^h u)=E+Pu,\qquad \gcd(P,D)=1.
```

Here $`H`$ is the partial first-division map. The shift preserves all earlier
guards, and the next high digit permutes endpoint residues.
Each legal parent has exactly $`m`$ disjoint legal children.
The first-division search is complete: success occurs at a delay
$`0,\ldots,m-1`$, while failure means no later division.
A depth-$`h`$ witness uses between $`h`$ and $`mh`$ raw ticks.

If $`I`$ is the set of infinitely-dividing seeds, then for every integer
$`X\ge1`$,

```math
\#(I\cap[1,X])\le m^h\lceil X/D^h\rceil,\qquad
\frac{\#(I\cap[1,X])}{X}\le(m/D)^h+\frac{m^h}{X}.
```

For $`m<D`$, fix $`h`$ first and then let $`X`$ increase; subsequently
increase $`h`$. This proves ordinary natural density zero, along the full
sequence of intervals. The sharper bound is

```math
\#(I\cap[1,X])\le mX^{\log m/\log D}.
```

Every complementary seed has one actual time $`t`$ after which there are
no divisions, and its exact full-clock tail is

```math
T^{t+j}(n)=q^jT^t(n)+c\sum_{i=0}^{j-1}q^i.
```

It escapes because $`c\ge1`$. Thus density-one seeds escape, but cycles
can remain in the exceptional set: $`(2,1,3)`$ has
$`1\to3\to1`$ with $`m=2<3`$. This also shows that $`m\mid D`$ is false;
only $`m\le D`$ is required.

[ResidueCylinders.lean](lean/ResidueCylinders.lean) proves the exact guards,
lifts, child count and raw-clock equivalence.
[ResidueDensity.lean](lean/ResidueDensity.lean) proves both interval estimates,
ordinary density and affine-tail recovery.

## Full-cycle boundary and negative drift

At $`m=D`$, every seed divides infinitely often. The strict-leakage fraction
is one and cannot prove eventual cessation of division.
Instead, every length-$`h`$ delay word has **one** source class modulo
$`D^h`$. Uniform classes therefore give an exact iid law:

```math
r_i\sim\operatorname{Uniform}\{0,\ldots,D-1\},\qquad
\mu=\frac{D-1}{2},\quad \sigma^2=\frac{D^2-1}{12}.
```

For a word with total delay $`R`$,

```math
H^h(n)=A_w n+C_w,\qquad A_w=q^R/D^h.
```

Set $`\gamma=\mu\log q-\log D`$. If $`\gamma<0`$, choose
$`\eta>0`$ with $`\rho=q^{\mu+\eta}/D<1`$.
For every good word $`R\le h(\mu+\eta)`$, $`A_w\le\rho^h`$.
The offset has a seed-independent bound

```math
C_w\le M_h=C_0\sum_{j=0}^{h-1}A_{\max}^j,\qquad
C_0=\frac{c}{D}\sum_{j=0}^{D-2}q^j,\quad
A_{\max}=\frac{q^{D-1}}D.
```

Thus good words give $`H^h(n)<n`$ whenever

```math
n\ge N_h=\left\lfloor\frac{M_h}{1-\rho^h}\right\rfloor+1.
```

The bad word fraction is at most $`\sigma^2/(h\eta^2)`$.
If $`E(X)`$ counts positive seeds at most $`X`$ whose raw trajectories
never fall below their initial value, then

```math
E(X)\le N_h+\frac{\sigma^2}{h\eta^2}(X+D^h).
```

Fixing $`h`$, taking $`X\to\infty`$, and then $`h\to\infty`$ proves
density-one strict descent. This is a deterministic integer theorem,
not an assumption of independent guards along one trajectory.
The compatible inverse-limit coding is a Bernoulli shift; the
[affine cocycle account](../QCD.ComplexCohomology.001/DynamicalCocycle.md)
explains its measured and cohomological meaning.

### Which full-cycle parameters have negative drift?

Under the stated positive hypotheses with $`q\ge2`$, the condition
$`\gamma<0`$ holds **exactly** for $`q=3,D=2`$ and odd $`c`$.
A full affine residue cycle has no fixed point; $`q=2`$ is excluded because
$`-c`$ is fixed. Thus $`q\ge3`$. For $`D\ge3`$, induction gives
$`3^{D-1}\ge D^2`$, and therefore $`\gamma\ge0`$.
At $`D=2`$, negative drift requires $`q<4`$, giving $`q=3`$;
full access is then equivalent to odd $`c`$.

The density-one descent theorem consequently includes every positive
odd offset in $`(3,c,2)`$. The exact word law holds for the other
full-cycle parameters too, but does not give this negative-drift estimate.
[BoundaryDrift.lean](lean/BoundaryDrift.lean) also proves the polynomial
growth inequality and the resulting arithmetic parameter restriction.

### Classical quantitative bound

For $`(q,c,D)=(3,1,2)`$, take $`h=8t`$ and $`\eta=1/8`$.
Words with at most $`5t`$ affine ticks have slope at most
$`(243/256)^t`$. Weighting a binary word with $`a`$ affine ticks by
$`5^a3^{8t-a}`$ gives

```math
\frac{\#\{a>5t\}}{2^{8t}}\le\beta^t,\qquad
\beta=\frac{65536}{84375}<1,\qquad
N_{8t}\le22\cdot256^t.
```

Consequently, for $`X\ge256/\beta`$,

```math
E(X)\le(22+2/\beta)X^{1-\alpha},\qquad
\alpha=\frac{\log(1/\beta)}{\log(256/\beta)}>0.
```

The [full written proof](tex/ResidueBoundary.tex) includes cylinder coding,
offset absorption and the simultaneous choice of depth and counting scale.
[BoundaryDrift.lean](lean/BoundaryDrift.lean) proves the finite weighted-word
bound, the good multiplier bound, the parameter restriction and the closing constants. It does
not yet formalize the complete inverse-limit or integer-density theorem.

Density-one descent does not imply that every classical seed reaches one:
the exceptional set and the behavior of later descending states require
additional control.

## Prime-square nonunit family

Let $`p`$ be prime and let $`Q,C\ge1`$ satisfy $`p\nmid QC`$.
For the raw parameters

```math
(q,c,D)=(pQ,pC,p^2),
```

density-one positive seeds enter the layer $`v_p(n)=1`$ and escape
in the full raw clock. This family has $`\gcd(q,D)=p\mid c`$;
it is not the older gcd-miss escape case.

After stripping finitely many initial $`p^2`$ factors, a unit $`u`$ has
$`Qu+C=p^v w`$ with $`w`$ a positive unit.

- For $`v=2a`$, one affine tick and $`a`$ divisions reach $`pw`$,
  the invariant layer.
- For $`v=2a+1`$, one affine tick and $`a+1`$ divisions reach $`w`$,
  a unit, in $`a+2`$ raw ticks.

A prescribed odd valuation word has relative unit density
$`p^{-\sum v_i}`$, and its total one-step surviving weight is

```math
\lambda=\sum_{a\ge0}p^{-(2a+1)}=\frac{p}{p^2-1}<1.
```

Finite high-valuation cutoffs and initial-factor cutoffs give the ordinary
upper-density bound

```math
\overline d\{\text{at least }h\text{ unit returns after stripping}\}
\le\frac{p}{p+1}\lambda^h.
```

Hence the never-entering set has density zero. In the layer, every tick is
affine and its exact geometric-sum tail escapes.
For $`(6,2,4)`$, $`\lambda=2/3`$.
An all-seed escape assertion would be false:
$`(2,2,4)`$ has $`1\to4\to1`$.

[NonunitResidues.tex](tex/NonunitResidues.tex) proves the complete counting
and integer recovery argument.
[NonCoprime.lean](lean/NonCoprime.lean) proves the invariant layer,
full-clock affine escape and legal prescribed odd-power block recovery.
The infinite density assertion is presently a written theorem.

The same formal companion also records the existing common-divisor
miss mechanism: if $`s\mid q,D`$ but $`s\nmid c`$, every positive orbit
strips its initial divisions and then has an affine tail.
This is already classified in
[QCD.AffineEscape.001](../QCD.AffineEscape.001/README.md), not an additional
new family.

## Exact finite computation

The generator retains jointly legal endpoints and raw division counts,
including immediate and consecutive divisions. It checks accepted and
rejected residue sources independently, and rejects unsupported nonunit
access calculations instead of inventing a return period.

The unit census covers 132 models, 660 depth rows, 75,490 parent classes,
898,742 raw-clock checks and 589,658 high-digit lifts.
The full-cycle census checks all words in its declared finite budgets,
their exact first two delay moments and their contracting-word counts.
For classical depth 12, it has 4,096 words, delay sum 24,576,
squared-delay sum 159,744 and 3,302 strictly contracting words.
These counts test the finite implementation; the theorems come from
the written recovery and the specified formal statements.

## Build and sources

```sh
lake build ResidueCylinders ResidueDensity BoundaryDrift NonCoprime
CGO_ENABLED=0 go test ./QCD.ResidueLeakage.001/go
make go GOFILE=QCD.ResidueLeakage.001/go/ResidueCylinders.go
make tex TEXFILE=QCD.ResidueLeakage.001/tex/ResidueBoundary.tex
make tex TEXFILE=QCD.ResidueLeakage.001/tex/NonunitResidues.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```

Related strict-leakage statements appear in `/home/dell/collatz/FINALEE.MD`,
Theorem 9.34. The [residue access family](../QCD.ResidueAccess.001/README.md)
supplies the finite affine return arithmetic. Negative-divisor density
variants, universal control of the full-cycle exceptional set, and general
nonunit families beyond the stated cases remain separate questions.
