<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Affine cocycles, cycle torsion and residue drift

Legal branch words provide a common algebra for homogeneous, additive,
common-base and residue-access dynamics. The useful object retains both the
linear part and the offset, together with its guards and raw clock.

## Exact composition

For the raw integer map with signed parameters, write a legal prefix as

```math
Q_n x_n=P_n x_0+B_n,\qquad
(P_0,Q_0,B_0)=(1,1,0).
```

An affine tick sends

```math
(P,Q,B)\longmapsto(qP,Q,qB+cQ),
```

and a legal division tick sends

```math
(P,Q,B)\longmapsto(P,dQ,B).
```

Both formulas follow by multiplying the actual next-state equation by
its denominator. Consequently $`P_n=q^{a_n}`$, $`Q_n=d^{b_n}`$ and
$`a_n+b_n=n`$. Induction proves the identity at every raw time.
For example, an affine tick followed by a division has
$`(P,Q,B)=(q,d,c)`$: it requires $`d\mid qx_0+c`$ as well as
$`d\nmid x_0`$. The algebraic formula does not replace either guard.

Over $`\mathbb Q`$, let an edge be $`x_{i+1}=A_i x_i+b_i`$.
Composition gives

```math
P=\prod_{i=0}^{r-1}A_i,\qquad
B=\sum_{j=0}^{r-1}
\left(\prod_{i=j+1}^{r-1}A_i\right)b_j,\qquad
x_r=Px_0+B.
```

The offset is ordered: interchanging edges generally changes it.
A closed word requires $`(1-P)x_0=B`$.
If $`P\ne1`$, it has at most one rational starting state; if $`P=1`$,
it closes only when $`B=0`$. Integral states, signs and branch conditions
remain separate reconstruction requirements.

## Cohomology retains offset obstructions

Change phase coordinates to $`v_i=x_i+t_i`$. Then

```math
v_{i+1}=A_i v_i+b_i+t_{i+1}-A_it_i.
```

For a closed phase word, $`t_r=t_0`$, so its return offset changes by
$`(1-P)t_0`$. Where all coefficients belong to a fixed ring, the class
of $`B`$ modulo $`(1-P)`$ is unchanged. Raw division has rational
coefficients; an integral obstruction must instead clear its denominators.

For odd-return equations with possibly different multipliers,

```math
D^{a_i}x_{i+1}-q_i x_i=c_i,
```

let $`M`$ be their cyclic integer matrix. Integral phase translation
changes the offset vector by $`Mt`$, preserving its class in
$`\operatorname{coker}M`$. Under $`a_i\ge1`$, $`D\ge2`$ and
$`\gcd(q_i,D)=1`$, [CycleArithmetic.md](CycleArithmetic.md) proves

```math
\operatorname{coker}M\cong\mathbb Z/|\Delta|\mathbb Z,\qquad
\Delta=D^{\sum a_i}-\prod q_i.
```

The weighted offset class vanishes exactly when every rational phase is
integral. Positive odd recovery still needs the appropriate sign and parity
hypotheses. The [three-letter criterion](../QCD.ThreeAffineClosure.001/README.md)
executes this distinction: positive determinant, odd multiplier and one
divisibility test reconstruct all phases and their exact valuations.

This is the relation to twisted cochains. A finite-field quotient detects
resonance after coefficient reduction, while the integer quotient retains
torsion and legal reconstruction. They are not interchangeable dynamics.

## What the specializations actually solve

### Homogeneous dynamics: offset vanishes

For $`c=0`$, the offset is zero along every word. For a scalar lattice seed
$`(x,y)\ne(0,0)`$, its content $`g=\gcd(|x|,|y|)>0`$ obeys the same
positive homogeneous rule with parameters $`|q|,|d|`$:

```math
g_n=|q|^{a_n}|d|^{-b_n}g_0,\qquad
g_0|x_n|=g_n|x_0|,\quad g_0|y_n|=g_n|y_0|.
```

These are exact identities on legal integral states.
A magnitude return forces $`|q|^a=|d|^b`$ with positive exponents.
Independence excludes every return and forces escape; dependence supplies
uniform coordinate bounds and a finite integral box, hence an actual periodic
tail. [Homogeneous lattice classification](../QCD.ComplexLattice.001/README.md#complete-homogeneous-scalar-classification)
proves the guard, proportionality and same-clock recovery.
The finite box is a real decrease to finitely many legal states, not a
classification obtained from the scalar cocycle alone.

### Additive dynamics: the offset must be retained

For $`q=1`$, $`P_n=1`$, but $`B_n`$ need not vanish.
A division-free tail is exactly $`x_{t+j}=x_t+jc`$.
The [positive additive classification](../QCD.Additive.003/README.md)
uses complete modular access to distinguish these escaping tails from bounded
finite cores. The closure equation by itself cannot distinguish a legal
cycle from an inadmissible rational solution. In particular, dropping $`B`$
would erase the effect of $`\gcd(c,D)`$.

### Common-base dynamics: a rank-one linear gain

For positive $`q=t^u,D=t^v`$, the linear part is
$`P_n/Q_n=t^{ua_n-vb_n}`$. The two multiplicative counters have one
exponent combination. At zero offset this becomes the solved exponent
recurrence; with nonzero offset the same gain does not determine the state.
[Common-base high-offset theorems](../QCD.CommonBase.001/README.md)
bound the offset and reconstruct all intermediate raw states.
The prime-exponent rank identifies the obstruction but does not silently
supply those bounds.

### Residue access: complete cylinders supply a law

Assume $`q\ge2,c\ge1,D\ge2,\gcd(q,D)=1`$.
A first-division block of delay $`r`$ has endpoint

```math
H_r(n)=\frac{q^r n+cS_r}{D},\qquad
S_r=\sum_{j=0}^{r-1}q^j,
```

and raw length $`r+1`$.
At full access $`m=D`$, every word of $`h`$ delays has exactly one source
class modulo $`D^h`$. Thus uniform counting on that finite quotient gives
**exactly**, not heuristically, independent uniform marks in
$`\{0,\ldots,D-1\}`$.

For the total delay $`R_h`$ and raw length $`T_h`$,

```math
\mathbb E R_h=h\mu,\quad
\operatorname{Var}R_h=h\sigma^2,\quad
T_h=h+R_h,\qquad
\mu=\frac{D-1}{2},\quad \sigma^2=\frac{D^2-1}{12}.
```

The logarithmic linear gain has mean

```math
\gamma=\mu\log q-\log D,\qquad
\frac{\mathbb E\log(q^{R_h}/D^h)}{\mathbb E T_h}
=\frac{\gamma}{1+\mu}.
```

This last expression is a ratio of finite expectations, not an asserted
limit along every integer orbit. For classical parameters it equals
$`\log(3/4)/3<0`$.

## Exact random law and ergodic interpretation

The compatible cylinder coding identifies the inverse limit
$`\mathbb Z_D=\varprojlim\mathbb Z/D^h\mathbb Z`$ with the one-sided full
shift, even when $`D`$ is composite. Uniform cylinder masses give the
Bernoulli product law. Deleting the first mark preserves this measure.

The shift is ergodic. If a measurable event $`E`$ is invariant, then for each
$`h`$ it is, up to a null set, the pullback of itself after deleting the first
$`h`$ marks. It is therefore independent of every cylinder determined by those
marks. Finite unions of cylinders approximate measurable events in measure;
applying this to $`E`$ gives $`\mathbb P(E)=\mathbb P(E)^2`$.
Hence invariant events have measure zero or one.

For an integrable gauge $`g`$, replace the log-gain observable $`L`$ by
$`L+g-g\circ H`$. Invariance gives
$`\int(g-g\circ H)=0`$: the mean $`\gamma`$ is unchanged.
This is an additive cohomological invariant of the specified measured
system. No independence assumption is made about an arbitrary chosen integer
trajectory. The countable integer subset has inverse-limit measure zero;
ergodicity alone says nothing about all its points.

The [boundary theorem](../QCD.ResidueLeakage.001/README.md#full-cycle-boundary-and-negative-drift)
bridges back to ordinary integer density. It fixes a finite depth, bounds
the bad word fraction, bounds every additive offset independently of the seed,
then takes the integer counting limit before increasing depth.
That recovery, not the random analogy alone, proves density-one strict descent.

For nonunit multipliers the coding changes. In the
[prime-square family](../QCD.ResidueLeakage.001/README.md#prime-square-nonunit-family),
odd valuation words have weight $`p^{-\sum v_i}`$.
Their total one-step surviving weight is
$`p/(p^2-1)<1`$; even valuations enter an invariant escaping layer.
Finite valuation and initial-factor cutoffs recover ordinary integer density.
This killed countable-alphabet mechanism is different from the uniform
full shift, although both retain exact branch words and clocks.

## Limits of the common algebra

The cocycle proves composition, closure, gauge invariance and the finite
counting gains above. It is not a complete orbit invariant. At $`m=D`$,
negative mean linear gain does not force every integer seed to descend:
offsets and exceptional words must be controlled for that same seed.
Classical universal arrival and the unclassified non-coprime families
remain separate obligations. No cohomological renaming closes them.

The general composition and ergodic arguments on this page are written
proofs. [AffineWords.lean](../Foundations.Main.StartHere/lean/AffineWords.lean)
and [ComplexLocalSystem.lean](lean/ComplexLocalSystem.lean) provide the
formal finite-word and field-quotient interfaces; the linked density papers
state explicitly which infinite assertions are not yet Lean declarations.
