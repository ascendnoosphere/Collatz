<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Affine escape behind the gcd division barrier

[Detailed proofs](tex/AffineEscape.tex) ·
[Formal proofs](lean/AffineEscape.lean) ·
[Exact arithmetic](go/AffineEscape.go) ·
[Arithmetic tests](go/AffineEscape_test.go)

For integers
$$
q\ge2,\qquad c\ge1,\qquad D\ge2,
$$
consider the positive raw map
$$
F(n)=
\begin{cases}
n/D,&D\mid n,\\
qn+c,&D\nmid n.
\end{cases}
$$
Put $g=\gcd(q,D)$ and assume
$$
g\nmid c.
$$

## QCD.AffineEscape.001.1 — the division barrier

For every positive integer $y$,
$$
D\nmid qy+c.
$$
Indeed, divisibility by $D$ would imply divisibility by $g$. Since
$g\mid qy$, it would then follow that $g\mid c$, contrary to the
hypothesis. Thus every affine instruction lands outside the division branch.

## QCD.AffineEscape.001.2 — canonical initial prefix

Given a positive seed $n$, there are unique integers $k\ge0$ and $x\ge1$
such that
$$
n=D^k x,
\qquad
D\nmid x.
$$
Here $k$ is the largest whole-base exponent for which $D^k\mid n$; no
primality assumption on $D$ is made. The first $k$ raw instructions are
exact divisions and
$$
F^k(n)=x.
$$

## QCD.AffineEscape.001.3 — exact tail and all-seed escape

Define
$$
G_0(q)=0,
\qquad
G_{j+1}(q)=qG_j(q)+1.
$$
Equivalently, because $q\ge2$,
$$
G_j(q)=\frac{q^j-1}{q-1}.
$$
For every $j\ge0$,
$$
F^{k+j}(n)=q^j x+cG_j(q),
\qquad
D\nmid F^{k+j}(n).
$$
The first assertion follows by induction, and the second is preserved at each
affine instruction by the division barrier. Since $x\ge1$,
$$
F^{k+j}(n)\ge q^j x\longrightarrow\infty.
$$
Consequently every positive seed escapes to infinity.

For example, at $(q,c,D)=(6,1,4)$ and $n=64$, the initial divisions give
$64\mapsto16\mapsto4\mapsto1$. The affine tail begins
$$
1\mapsto7\mapsto43\mapsto259\mapsto1555,
$$
and every displayed tail state is nonzero modulo $4$.

## Reduction status

**Original obligation.** Classify every positive raw orbit in a parameter cell
satisfying $\gcd(q,D)\nmid c$.

**Replacement obligations.** Extract the maximal initial power $D^k$ from the
seed and evaluate the explicit affine formula.

**Recovery.** The initial division identity and the tail formula reconstruct
every raw state, with its exact time index and branch guard.

**Strict decrease.** After the finite prefix, the number of unresolved future
branch choices is zero: no later division is possible. The remaining recurrence
is explicit and has the lower bound $q^j x$.

The condition is sufficient, not necessary. If $\gcd(q,D)\mid c$, this result
gives no classification. It also makes no claim for signed states, signed
coefficients, or $q<2$, and it does not address the classical cell
$(3,1,2)$, where the gcd condition necessarily fails.
