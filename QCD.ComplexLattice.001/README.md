<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Scalar dynamics on imaginary quadratic lattices

For zero offset and signed scalar magnitudes at least two, all nonzero
lattice states are classified: independent magnitudes give full-sequence
complex-norm escape; dependent magnitudes give eventual periodicity.
For arbitrary integer offsets, independence still proves escape of every
nonreal state. The integer axis for nonzero offsets retains the corresponding
signed integer problem.

For raw $`(3,c,2)`$ with odd $`c`$, a complementary dyadic argument gives
an explicit entry time into a division-free tail. The general independence
argument allows infinitely many divisions and does not supply that clock bound.

[Homogeneous Lean classification](lean/HomogeneousLattice.lean) ·
[Homogeneous detailed proof](tex/HomogeneousLattice.tex) ·
[General scalar Lean proof](lean/ScalarEscape.lean) ·
[General scalar detailed proof](tex/ScalarEscape.tex) ·
[Dyadic Lean proofs](lean/ComplexLattice.lean) ·
[Dyadic detailed proof](tex/ComplexLattice.tex) ·
[Exact arithmetic foundations](../QCD.QuadraticArithmetic.001/README.md) ·
[Visual survey and Go checks](../QCD.ComplexDynamics.001/README.md)

## Rings, not interchangeable fields

Let

```math
R=\mathbb Z[\theta],\qquad \theta^2=\tau\theta-\nu,
\qquad \tau,\nu\in\mathbb Z,\quad 4\nu>\tau^2.
```

Use the complex embedding

```math
\theta=\frac{\tau+i\sqrt{4\nu-\tau^2}}2,\qquad z=x+y\theta.
```

Gaussian integers use $`(\tau,\nu)=(0,1)`$ and $`\theta=i`$.
Eisenstein integers use $`(\tau,\nu)=(-1,1)`$ and
$`\theta=\omega=e^{2\pi i/3}`$. The second coefficient $`y`$ is **not**
$`\operatorname{Im}z`$ in the Eisenstein basis: there
$`\operatorname{Re}z=x-y/2`$ and $`\operatorname{Im}z=\sqrt3y/2`$.
These are coordinate orders, not a claim that every number field has such a basis.

The raw lattice map is

```math
T(z)=\begin{cases}z/2,&z\in2R,\\3z+c,&z\notin2R.\end{cases}
```

Because $`1,\theta`$ are an integral basis, $`2\mid z`$ in $`R`$ exactly when
$`2\mid x`$ and $`2\mid y`$. In particular, Gaussian division by $`2`$ is
not division by $`1+i`$. The latter has the different guard $`x\equiv y\pmod2`$.
Literal divisibility over a field would collapse this map to $`z/2`$;
[the field obstruction](../QCD.ComplexCohomology.001/README.md) is proved separately.

### Formal recovery in the actual ring

The checked `LatticeRing tau nu` is Mathlib's free integral quadratic algebra,
not just a pair with an assumed divisibility predicate. `ScalarTwoDivides`
proves its actual element guard. `ScalarTwoQuotient` reconstructs a legal
integral quotient; `ScalarTwoUnique` proves uniqueness even if the general
quadratic algebra has other zero divisors. `RawCoordinates` and
`CoordinatesIter` intertwine the ring map with the coordinate map at every
original raw time. `QuadraticOffAxisEscape` is the resulting ring-element height theorem.
`ImaginaryGeneratorRoot` and `ImaginaryGeneratorPositive` verify the explicit
complex root and its strictly positive imaginary part. `ImaginaryEmbedding`
is an actual algebra map; `ImaginaryEmbeddingInjective` proves that it loses
no lattice states. Its exact imaginary-part formula and
`ImaginaryEmbeddingNorm` retain the fixed transverse scale.
`ComplexOffAxisEscape` then proves the displayed full-sequence statement
in the actual complex norm, with every real bound quantified.

## Complete homogeneous scalar classification

Set $`c=0`$, $`|q|,|d|\ge2`$, and $`z_0=x_0+y_0\theta\ne0`$.
Then exactly one of the following parameter cases applies:

1. If $`|q|`$ and $`|d|`$ are multiplicatively independent,
   $`|T^n(z_0)|\to\infty`$ along the full raw sequence.
2. If $`|q|^a=|d|^b`$ for some positive $`a,b`$, the orbit is eventually
   periodic and at every raw time satisfies

```math
|x_n|\le|q||d||x_0|,\qquad
|y_n|\le|q||d||y_0|.
```

Zero is fixed. Both coefficient signs are retained, and the theorem includes
nonzero integer-axis seeds.

The reconstruction invariant is the content
$`g_n=\gcd(|x_n|,|y_n|)>0`$. Bézout's identity proves that
$`d\mid x_n`$ and $`d\mid y_n`$ exactly when $`|d|\mid g_n`$.
Consequently $`g_n`$ follows the positive homogeneous map with parameters
$`|q|,|d|`$. Exact multiplication and division also preserve

```math
g_0|x_n|=g_n|x_0|,\qquad g_0|y_n|=g_n|y_0|.
```

Independence gives content escape. A nonzero transverse coordinate recovers
complex-norm escape through its fixed imaginary scale; if the transverse
coordinate is zero, height is the absolute integer coordinate.
Dependence gives $`g_n\le|q||d|g_0`$, and the proportionality identities give
the two coordinate bounds. The orbit then lies in a finite box of integral
pairs. A repeated pair and determinism yield a full periodic tail.
Same-clock coordinate recovery transfers that tail to actual ring elements.

[HomogeneousLattice.lean](lean/HomogeneousLattice.lean) proves the guard,
content recursion, proportions, bounds, finite-state argument and both ring
conclusions. It does not assert a primitive-period formula for signed
dependent lattice states. The [positive scalar formula](../QCD.Homogeneous.002/README.md)
has its own stronger period statement and parameter hypotheses.

## General scalar escape by arithmetic independence

For the signed raw scalar map

```math
T_{q,c,d}(x+y\theta)=
\begin{cases}
(x/d)+(y/d)\theta,&d\mid x\text{ and }d\mid y,\\ (qx+c)+qy\theta,&\text{otherwise},
\end{cases}
```

let $`a_n,b_n`$ count affine and division ticks. The exact transverse identity is

```math
a_n+b_n=n,\qquad d^{b_n}y_n=q^{a_n}y_0.
```

It does **not** replace the common guard by a guard on $`y`$ alone.
If $`y_0\ne0`$, any repeated magnitude $`|y_i|=|y_j|`$, $`i<j`$,
would give $`|q|^a=|d|^b`$ on that actual segment, with $`a,b>0`$.
Multiplicative independence excludes every such collision. Hence every bounded
set of nonnegative integer magnitudes is visited finitely often, proving
$`|y_n|\to\infty`$ along the full sequence. The same positive transverse
embedding scale recovers $`|T^n(z)|\to\infty`$.

A finite sufficient certificate is a nonzero prime-exponent minor:

```math
v_p(|q|)v_r(|d|)-v_r(|q|)v_p(|d|)\ne0.
```

Coprime magnitudes at least two satisfy independence. Coprimality is not
necessary: for $`12=2^2\cdot3`$ and $`18=2\cdot3^2`$, the minor is
$`2\cdot2-1\cdot1=3`$. Thus all nonreal seeds escape for raw
$`(12,c,18)`$, for every integer $`c`$.

**Infinitely dividing control.** For $`(12,0,18)`$ and seed $`\theta`$,

```math
8^j\theta\longmapsto12\cdot8^j\theta
\longmapsto144\cdot8^j\theta\longmapsto8^{j+1}\theta.
```

The third tick divides in every block. An eventual-affine-tail argument would
miss this family. Independence gives no monotonicity or uniform effective
last-visit bound.

**Dependent control.** For raw $`(4,0,8)`$, there is a primitive nonreal five-cycle:

```math
\theta\to4\theta\to16\theta\to2\theta\to8\theta\to\theta,
\qquad4^3=8^2.
```

`ScalarEscape.lean` proves actual scalar divisibility and unique quotient,
all-clock coordinate recovery, transverse injectivity and escape, both
controls, and the complex-norm statement. Its namespace is
`GeneralizedCollatz.ScalarEscape`; the quantitative dyadic module retains
`GeneralizedCollatz.ComplexLattice`.

### Same-clock conjugacy between different orders

Coefficient matching $`x+y\theta\mapsto x+y\theta'`$ is a bijective
same-clock conjugacy for fixed scalar $`q,c,d`$. It preserves every state,
branch, period and return time. It is **not** generally a ring homomorphism:
matching $`i`$ to $`\omega`$ sends $`i^2`$ to $`-1`$, but
$`\omega^2=-1-\omega`$. Thus the scalar dynamical systems are isomorphic,
while their multiplication tables, nonscalar divisors and ideal arithmetic
remain distinct. `OrderTransferRaw`, `OrderTransferIterate` and
`OrderTransferNotMultiplicative` formalize this separation.

## Decreasing dyadic rank and exact recovery

For $`y\ne0`$, write $`y=2^r u`$ with $`u`$ odd, allowing either sign.
Until $`y`$ becomes odd:

- If $`x`$ is even, one raw division removes one factor of $`2`$ from $`y`$.
- If $`x`$ is odd, the affine tick makes $`3x+c`$ even, since $`c`$ is odd.
  It preserves the dyadic rank of $`y`$. The next raw tick divides both
  coordinates and removes one factor of $`2`$.

Thus an odd transverse coefficient is reached at some raw time $`t\le2r`$.
After that, no further division is possible, and the exact tail is

```math
y_{t+j}=3^j y_t,\qquad
 x_{t+j}=3^j x_t+c\sum_{k=0}^{j-1}3^k.
```

The complex norm satisfies
$`|T^{t+j}(z)|\ge|\operatorname{Im}\theta|\,3^j|y_t|\to\infty`$.
All finite coordinate cycles therefore lie on the real axis. No positive
integer convergence theorem follows.

**Original obligation:** classify nonreal raw $`(3,c,2)`$ orbits, with odd real $`c`$.
**Replacement obligations:** remove the finite rank $`r=v_2(|y|)`$, then solve the
odd transverse affine tail. **Recovery:** every block is one or two original
raw ticks with its original guard; the displayed tail supplies every later
state. **Difficulty decrease:** each unresolved block strictly removes one
of $`r`$ factors of two, with at most $`2r`$ ticks before a solved tail.
**Preservation conditions:** scalar divisor $`2`$, scalar multiplier $`3`$, odd
real integral offset, integral basis, and nonzero second coefficient.
Even offsets, complex offsets, rotated multipliers and ramified divisors
are not covered by this descent.

## A different complex family really does have nonreal cycles

For a residue $`r(z)=(x\bmod2)+(y\bmod2)\theta`$, define instead

```math
J_\pm(z)=
\begin{cases}
z/2,&r(z)=0,\\ (3z\pm r(z))/2,&r(z)\ne0.
\end{cases}
```

Each numerator lies in $`2R`$. The plus Gaussian convention is the four-residue
Joseph map described by Kucinski [Kucinski00], **not** the raw map $`T`$.
The Eisenstein and minus variants are explicitly specified extensions here;
they are not attributed to that paper.

In either coordinate ring, the following are exact:

```math
1+\theta\xrightarrow{J_+}2+2\theta\xrightarrow{J_+}1+\theta,
\qquad J_+(-1-\theta)=-1-\theta,
\qquad J_-(1+\theta)=1+\theta.
```

These nonreal cycles demonstrate why the raw escape theorem cannot be
transferred to a residue-wise quotient convention. One $`J`$ tick has its
own clock; no conjugacy with a fixed-offset raw map is asserted.

![Gaussian raw minus: off-axis escape and signed real cycles](../QCD.ComplexDynamics.001/other/GaussianMinus.svg)

Navy cells have a proved escaping tail. Other colors mark exact cycles
found in the stated finite seed window. These are lattice cells, not a
continuous orbit on $`\mathbb C`$ or a Julia set.

## Proof interfaces and computation

`TwoGuard`, `FiniteOddEntry`, `DyadicDecomposition`, `OddTailImag`,
`OddTailReal`, `OddTailHeight` and `OffAxisEscape` prove the raw descent,
both exact tail coordinates and full-sequence height escape.
`ImaginaryEmbeddingInjective` and `ComplexOffAxisEscape` complete recovery
in the original complex norm. `ResidueNumerators`, `NonrealResidueCycle` and `NonrealResidueFixed`
check the competing quotient convention. `ResidueNonDescent` gives
$`0\equiv2\pmod2`$ but different raw successor residues: a raw map does
not automatically descend to a finite ring.

The survey tests signed quotient arithmetic independently with `big.Rat`,
replays dyadic ranks through $`r=10`$ for $`c=\pm1`$, checks the raw-versus-quotient
negative control, and renders both lattice embeddings. These are finite
implementation checks; universality comes from the written and Lean proofs.

```bash
make lean
CGO_ENABLED=0 go test ./QCD.ComplexDynamics.001/go
make tex TEXFILE=QCD.ComplexLattice.001/tex/ComplexLattice.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```

Open: nonzero-offset real-axis all-seed behavior, other complex parameter families, and
infinite basin geometry for $`J_\pm`$. A finite survey is not an exhaustive cycle
classification for the infinite lattice.

## Source scope

[Kucinski00] Gina I. Kucinski, *Cycles for the $`3x+1`$ map on the Gaussian
integers*, May 2000, [author-hosted preprint](https://monks.scranton.edu/files/pubs/kucinski.pdf).
Its Gaussian convention and reported cycle bounds concern $`J_+`$, not $`T`$;
those bounds are not assumed in the raw escape proofs.
