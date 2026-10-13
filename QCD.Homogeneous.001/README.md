<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# QCD.Homogeneous.001

## Multiplicatively independent homogeneous maps

Let
$$
T_{q,D}(n)=
\begin{cases}
n/D,&D\mid n,\\
qn,&D\nmid n,
\end{cases}
\qquad q,D\ge2,
\qquad n\in\mathbb N_{>0}.
$$
Division has precedence, and every iterate is counted at the raw
one-instruction clock.

The pair $(q,D)$ is **multiplicatively independent** when
$$
q^a\ne D^b
\qquad(a,b\in\mathbb N_{>0}).
$$
This condition is not coprimality: $(6,4)$ is independent despite its common
factor.

## Closed result

For every multiplicatively independent pair $(q,D)$ and every positive seed
$n$, the raw orbit
$$
k\longmapsto T_{q,D}^{\langle k\rangle}(n)
$$
is injective and tends to infinity. Thus, for every bound $B$, all
sufficiently late raw iterates exceed $B$. The conclusion is stronger than
unboundedness and stronger than the absence of periodic orbits.

A legal raw word with $A$ affine instructions and $E$ division instructions
has exact homogeneous data
$$
(P,B,Q)=(q^A,0,D^E).
$$
If a nonempty word returned a positive state to itself, guarded word closure
would force $q^A=D^E$. Both counts must be positive, contradicting
multiplicative independence. Any collision between two orbit times would give
such a return at the earlier positive state, so the orbit is injective. An
injective sequence of positive integers visits a bounded finite interval only
finitely many times; hence the complete sequence tends to infinity.

## Exact dependence decision

The arbitrary-precision checker decides whether positive powers coincide
without factoring the coefficients. It merges the increasing power lists
$$
q,q^2,\ldots,q^{L_D}
\quad\text{and}\quad
D,D^2,\ldots,D^{L_q},
$$
where the binary bit lengths of $D$ and $q$ suffice for $L_D$ and
$L_q$. If any relation exists, unique factorization gives a reduced one
within these bounds. Every reported relation is an exact integer equality.

The large control
$$
(2^{100})^{101}=(2^{101})^{100}
$$
is detected with exponents $(101,100)$.

## Artifacts

- [Detailed proof](tex/Homogeneous.tex)
- [Lean proof](lean/Homogeneous.lean)
- [Arbitrary-precision checker](go/Homogeneous.go)
- [Executable tests](go/Homogeneous_test.go)

The Lean development proves the exact guarded word law, excludes every
nonempty positive return, identifies the natural map with the foundational
signed raw map on natural casts, proves raw-time injectivity, and concludes
convergence to the top filter on $\mathbb N$.

The Go tests check all coefficient pairs $2\le q,D\le128$ against a redundant
exact power search. They also verify $27060$ independent-orbit certificates,
covering $432960$ endpoint-inclusive states for $2\le q,D\le32$, seeds
$1\le n\le30$, and fifteen raw instructions. These checks validate the
implementation; the Lean theorem supplies the universal result.

## Boundary

This result does not classify multiplicatively dependent pairs. It also does
not cover $q=1$, $D=1$, zero or negative states, signed divisors, or nonzero
offsets. No conclusion about those separate regimes is inferred here.
