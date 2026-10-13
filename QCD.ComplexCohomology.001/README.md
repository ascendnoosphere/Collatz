<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# QCD.ComplexCohomology.001 — Cycle cochains and affine holonomy

**Closed obligations:** explicit ordinary and twisted cochains on finite
cycles; exact affine reconstruction over any field; and the obstruction to
using field divisibility as a nontrivial branch guard. This is graph cohomology
with specified coefficients, **not** a claim to have constructed a Galois,
étale, or ambient-plane cohomology theory for every Collatz family.

[Cycle and transport proofs](lean/ComplexCohomology.lean) ·
[Functional-graph proofs](lean/ComplexGraph.lean) ·
[Local-system quotients](lean/ComplexLocalSystem.lean) ·
[Detailed proofs and audit](tex/ComplexCohomology.tex) ·
[Exact finite-field checks](../QCD.ComplexAtlas.001/go/ComplexAtlas_test.go) ·
[Visual atlas](../QCD.ComplexAtlas.001/README.md)

## A field is a coefficient domain, not a lattice divisibility test

For a field $K$ and $d\ne0$, every $z\in K$ is divisible by $d$, because
$z=d(z/d)$. Thus the literal rule

$$
T(z)=\begin{cases}z/d,&d\mid z,\\qz+c,&d\nmid z\end{cases}
$$

collapses to $T(z)=z/d$, independently of $q,c$. This includes number fields,
$\mathbb C$, and finite fields. Nontrivial lattice branching instead requires
a subring and an integral divisibility predicate, or a separately specified
partition. A **state ring** and a **cochain coefficient field** are different
data; the computations below keep them separate.

A raw lattice map also need not descend modulo its divisor: the equal
classes of $0$ and $2$ modulo $2$ have raw successors $0$ and $1$.
The finite-ring examples below therefore use a genuine affine map on the
quotient ring, not an invented quotient of raw halving.

## Ordinary cohomology computes, but forgets, cycle length

For an oriented cycle with $n\ge1$ edges and an abelian coefficient group $A$,
set

$$
C^0=A^n,\qquad C^1=A^n,\qquad
(\delta f)_j=f_{j+1}-f_j,\qquad f_n=f_0.
$$

There are no two-cells. The complete test for exactness is

$$
a\in\operatorname{im}\delta
\quad\Longleftrightarrow\quad
\Pi(a):=\sum_{j=0}^{n-1}a_j=0.
$$

**Proof and recovery.** Differences telescope. Conversely, for zero period,
$f_j=\sum_{k<j}a_k$ supplies one common potential on every edge and satisfies
$f_n=f_0$. A cochain supported on one marked edge realizes any prescribed
period. Equal periods are exactly equal classes. Zero differences force a
constant potential. Consequently

$$
H^0\cong A,\qquad H^1=C^1/\operatorname{im}\delta\cong A,
$$

including a one-edge self-loop and fields whose characteristic divides $n$.
No division by $n$ or averaging is used. For $n=0$ there is no nonempty cycle;
the period-surjectivity assertion is not made.

For a finite functional graph with $N$ vertices and $k$ weak components,
there is one edge per vertex and one directed cycle per component.
Over a field, constant potentials on each component give
$\dim H^0=k$, hence $\operatorname{rank}\delta=N-k$ and
$\dim H^1=N-(N-k)=k$. Incoming trees do not add independent periods.
`ComponentKernelEquiv` constructs the linear isomorphism from the actual
incidence kernel to functions on the generated weak-component quotient.
`GraphH0Dimension`, `GraphIncidenceRank`, and `GraphH1Dimension` prove all
three formulas for every finite functional graph, including an empty graph
and self-loops, in every field characteristic.

**Method obstruction:** a cycle of length two and a cycle of length three
both have $H^1\cong A$. Unmarked cohomology alone cannot recover the raw period,
coordinates, signs, branch guards, or reachability from a particular seed.
Keep those marks rather than declaring them consequences of the group.

## Twisted cochains recover an affine word

Let $K$ be any field and let the $j$th edge carry
$z_{j+1}=\lambda_jz_j+a_j$. For a rank-one local system require
$\lambda_j\in K^\times$. Define

$$
(\delta_\lambda f)_j=f_{j+1}-\lambda_jf_j,
\qquad
P=\prod_{j=0}^{n-1}\lambda_j,
\qquad
B=\sum_{j=0}^{n-1}\left(\prod_{k=j+1}^{n-1}\lambda_k\right)a_j.
$$

The products over empty index sets are $1$. Direct ordered composition gives

$$
z_n=Pz_0+B,\qquad (1-P)z_0=B.
$$

- If $P\ne1$, the unique periodic potential starts at $z_0=B/(1-P)$;
  every edge cochain is exact, and $H^0=H^1=0$.
- If $P=1$, exactness is equivalent to $B=0$. Every initial value then
  closes. The weighted period realizes all of $K$ (the last edge has weight
  $1$), so $H^0\cong H^1\cong K$.

`TwistedExactIff` constructs a single potential by the same transport recurrence;
`NonneutralTwistedExact` and `NeutralTwistedExact` prove both cases.
`TwistedCoboundaries` is a submodule defined by genuine shared periodic
potentials, not by assuming the closing conclusion. `NeutralImageKernel`
identifies it with the linear weighted-period kernel, while
`NonneutralImageTop` identifies the nonneutral image with the entire edge
space. The actual quotient `FirstTwistedCohomology` has the checked
`NeutralH1Equiv` to $K$ for $n\ge1$; `NeutralH0Equiv` evaluates and
reconstructs homogeneous potentials. The two `NonneutralH0Zero` and
`NonneutralH1Zero` theorems prove the nonneutral dimensions vanish.
The transport identities themselves remain valid when some multipliers
vanish, but that stronger algebraic statement is not called a local system.

This is useful because an affine word is replaced by a **scalar closing
equation with explicit coordinate recovery**. It does not settle which words
are admissible for a branching map.

### What the lattice recovery still requires

For a raw $q,c,d$ word with $a$ affine ticks and $b$ division ticks,
$P=q^a/d^b$ and write $B=cU/d^b$, where $U$ retains the ordered branch data.
When $d^b\ne q^a$, the candidate seed is

$$
z_0=\frac{cU}{d^b-q^a}.
$$

It is a cycle only if **the same candidate** belongs to the state ring,
all reconstructed division ticks are integral, and every affine tick has
$d\nmid z_j$. The neutral case $d^b=q^a$ requires $cU=0$ and all the same
guards. A field solution without these tests is not a certified lattice cycle.

For example, the raw real minus cycle $1\to2\to1$ has
$(\lambda_0,\lambda_1)=(3,1/2)$ and $(a_0,a_1)=(-1,0)$.
Thus $P=3/2$, $B=-1/2$, and $z_0=1$.
Over $\mathbb F_3$, the integer multiplier $3$ is zero: this is not the
same invertible local system. Coefficient reduction must check every denominator
and multiplier, not just replace a characteristic label.

## Finite fields versus ramified finite rings: executed census

The test map is $A(z)=\theta z+1$ on each finite quadratic quotient.
All four maps are permutations because $\theta$ is a unit. The columns of
ranks use the **independent** cochain coefficient fields
$\mathbb F_2,\mathbb F_3,\mathbb F_5$.

| State ring | States | Directed cycle lengths | $\dim H^1$ | Incidence ranks over the three fields |
|---|---:|---|---:|---|
| $\mathbb Z[i]/(2)$, ramified, not a field | 4 | 4 | 1 | 3, 3, 3 |
| $\mathbb Z[i]/(3)\cong\mathbb F_9$ | 9 | 1, 4, 4 | 3 | 6, 6, 6 |
| $\mathbb Z[\omega]/(2)\cong\mathbb F_4$ | 4 | 1, 3 | 2 | 2, 2, 2 |
| $\mathbb Z[\omega]/(3)$, ramified, not a field | 9 | 3, 3, 3 | 3 | 6, 6, 6 |

Over $\mathbb F_2$, $X^2+1=(X+1)^2$ has a nonzero nilpotent in the Gaussian
quotient; $X^2+X+1$ is irreducible, giving the Eisenstein field $\mathbb F_4$.
Over $\mathbb F_3$, these roles reverse: $X^2+1$ is irreducible, while
$X^2+X+1=(X-1)^2$. The actual Frobenius automorphisms and complete two-element Galois groups
are now checked in [ComplexFields.lean](../QCD.ComplexAtlas.001/lean/ComplexFields.lean).
Conjugation transports affine orbits with both parameters and the same clock;
it does not convert the affine permutations into raw Collatz maps. The
[census](../QCD.ComplexAtlas.001/README.md#actual-quadratic-galois-fields-with-ramified-negative-controls)
tests matrix ranks, inverses, roots, Frobenius laws and the two ramified controls.

## Reduction status and limits

**Certified finite-cycle calculation:** the closing problem over a field
reduces to $P,B$ and the displayed scalar equation; recovery constructs all
vertices in $n$ successive steps. The unresolved work decreases from $n$
unknown vertex values to one scalar, without an existence oracle.
**Preserved:** the edge order, multipliers, offsets, coefficient field, endpoint
condition and chosen orientation. **Not removed:** word enumeration, infinite
lattice admissibility, all-seed convergence, or a fractal-to-arithmetic transfer.

**Refuted source routes:** a square finite matrix with nonzero determinant
has zero kernel; the all-ones vector is not automatically a cocycle of a
weighted matrix. For example, $\lambda=2$ on a one-edge cycle over $\mathbb Q$
gives $\delta_\lambda=[-1]$ and $H^0=H^1=0$. Zero group homomorphisms always
exist; only additional mark-preserving or surjectivity requirements can exclude
bonding maps. For the shortcut/Joseph scalar rules, an $n$-tick word with
$a$ nonzero-residue ticks has $P=3^a/2^n\ne1$ when $n\ge1$, so it determines
at most one periodic seed. There are finitely many words at each length;
these periodic points are therefore countable, not a continuum merely because
the ambient $2$-adic space is uncountable. This countability argument requires
nonneutral holonomy: an identity map has an entire continuum of fixed points.
Historical source locations and dispositions are recorded in
[ResearchAudit.md](../QCD.ComplexAtlas.001/ResearchAudit.md).

```bash
make lean
CGO_ENABLED=0 go test ./QCD.ComplexAtlas.001/go
make tex TEXFILE=QCD.ComplexCohomology.001/tex/ComplexCohomology.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```

The Lean file proves ordinary periods, common-potential recovery, the twisted
exactness criteria, and field collapse. `ExactCochainsIff` identifies the finite
kernel with actual cycle coboundaries; `FirstCohomologyEquiv` is a checked
`LinearEquiv` from the finite-cochain quotient to the coefficient field.
`FirstCohomologyPeriod` checks its action on each concrete class.
`ComplexGraph.lean` proves the general functional-graph dimension formulas
using actual weak components and the incidence cokernel.
`ComplexLocalSystem.lean` proves the twisted quotient and homogeneous
potential isomorphisms, plus both zero-dimension alternatives. The four
finite-ring instances and local-system cases are independently checked in Go.
The graph invariant does not solve the original universal Collatz targets.
