SPDX-License-Identifier: CC-BY-4.0

# Division-free escape and zero-avoiding residue cycles

Let $q,c,d\in\mathbb Z$ satisfy $|q|\ge2$ and $|d|\ge2$. Set $m=|d|$ and
$$
A(n)=qn+c,\qquad z(n)=(q-1)n+c,\qquad f(r)=(qr+c)\bmod m.
$$
The raw map divides the current state by $d$ when $d$ divides it, and otherwise
applies $A$. The zeroth raw state is the seed.

## Cycle criterion

The following are equivalent:

1. Some positive integer seed has a raw orbit that is never divisible by $d$
   and whose absolute values tend to infinity.
2. The finite map $f$ has a cycle contained in $\{1,\ldots,m-1\}$.

One undivided step satisfies
$$
z(A(n))=qz(n),\qquad A(n)\bmod m=f(n\bmod m).
$$
Hence
$$
z(A^j(n))=q^jz(n),\qquad (q-1)A^j(n)=q^jz(n)-c.
$$
If $z(n)\ne0$, then for every $N\in\mathbb N$ and every
$j\ge |c|+N|q-1|+1$,
$$
|q|^j|z(n)|\ge2^j>|c|+N|q-1|,
$$
so the normal form gives $|A^j(n)|>N$. This is eventual growth of the full
sequence, not merely unboundedness along a subsequence.

A cycle state $r$ has the positive lift $r+m$ or $r+2m$ with nonzero
displacement. The two displacements differ by $(q-1)m\ne0$, so they cannot
both vanish. The lifted affine orbit stays on the residue cycle and never
becomes divisible by $d$. Induction therefore identifies it with the raw orbit.
The normal form proves the required growth.

Conversely, a division-free raw orbit follows $f$ on nonzero residues. A
repeated residue cuts out a nonzero cycle. A nonzero cycle also exists exactly
when some residue $r<m$ satisfies $f^j(r)\ne0$ for every $j\in\mathbb N$;
equivalently, not every residue eventually reaches zero.

## Finite-window bound

The cycle extraction needs only the raw states at indices $0,\ldots,m-1$.
If none is divisible by $d$, their $m$ residues occupy a set of $m-1$ nonzero
values. Two indices $i<j<m$ have the same residue. The block from $i$ through
$j-1$ follows $f$ and closes at its first state, giving a zero-avoiding cycle.

Consequently, if no zero-avoiding cycle exists, then for **every integer seed**
$n$ there is an index $j<m$ at which the raw state is divisible by $d$. The
transition from index $j$ to $j+1$ then uses division. This bound does not
require $|q|\ge2$; that hypothesis is needed for the escape direction.

## Computed examples

- $(q,c,m)=(2,1,3)$: residue $2$ is fixed, and the positive lift $5$ has
  $A^j(5)=6\cdot2^j-1\equiv2\pmod3$.
- $(2,0,3)$: the nonzero residues form $1\mapsto2\mapsto1$; the lift $4$ has
  $A^j(4)=4\cdot2^j$.
- $(2,0,2)$: residue $1$ maps to $0$. Every even seed is immediately divisible,
  and every odd seed becomes divisible after one affine step.
- $(-3,2,5)$: residue $3$ is fixed, and
  $A^j(8)=(15(-3)^j+1)/2\equiv3\pmod5$. The state signs alternate while the
  magnitudes diverge.
- $(2,-3,2)$: residue $1$ is fixed, but lift $3$ has zero displacement and is
  an affine fixed point. The second lift $5$ has
  $A^j(5)=3+2^{j+1}$ and escapes without division.

## Reduction record

- **Original obligation:** for fixed $q,c,d$ under the stated hypotheses,
  decide whether a positive seed has a division-free raw orbit whose absolute
  values tend to infinity.
- **Replacement obligation:** decide whether $f$ has a nonzero residue cycle.
- **Recovery:** lift a cycle state by one of the two explicit positive candidates;
  nonzero displacement gives growth. In the other direction, the first $m$
  division-free states suffice to extract a cycle.
- **Difficulty decrease:** an infinite seed-and-time search is replaced by a
  finite map with $m$ states. A direct search uses at most $m-1$ starts and $m$
  inspections per start. This proves termination, not efficiency in the bit
  length of $m$.
- **Preservation:** the same integers $q,c,d$, positive-seed requirement, raw
  state clock, division-freeness, and full-sequence escape conclusion are kept.
  Divisibility by $d$ is equivalent to divisibility by $|d|$; the signed
  quotients themselves are not identified.

## Finite arithmetic certificate

The checked rectangle is
$$
q\in\{-5,-4,-3,-2,2,3,4,5\},\qquad -5\le c\le5,\qquad 2\le m\le6.
$$
Displacement and residue identities are checked at every $-8\le n\le8$.
There are **440** parameter triples, of which **312** have a zero-avoiding
cycle. Each returned residue is checked for cycle closure; every unsuccessful
case is checked for zero-reaching from every residue.

Each successful case receives a positive lift and eight affine steps. The
nine visited states retain nonzero residues and the displacement recurrence.
The bounds are
$$
0<n\le17,\qquad |A^j(n)|\le7{,}128{,}905\quad(0\le j\le8),
$$
$$
|z(A^j(n))|\le42{,}773{,}435<2^{26}.
$$
The normal form also gives
$$
|A^8(n)|\ge\frac{2^8-5}{6}>17\ge n,
$$
which justifies the terminal growth check uniformly on the rectangle.

There are **23,286** recorded comparisons. The separating-equality check is
part of the actual certificate: a predicate accepting every comparison is
rejected without skipping the other rows. Unsupported machine inputs are
rejected before arithmetic or bit shifts. The arithmetic primitives accept
only the stated multiplier and offset ranges and operand magnitude at most
$42{,}773{,}435$; their affine and displacement outputs have magnitude below
$2^{28}$. The cycle functions accept only $2\le m\le6$.

Tests use arbitrary-precision integer arithmetic and a different graph
algorithm: repeatedly remove zero and its predecessors. This checks the
machine calculations, the cycle decisions, the returned witnesses, and the
lifted paths. The sequential checking loops allocate no heap memory. The
executable assigns the eight multiplier slices to separate workers with
disjoint counters.

These finite counts do not imply a density over unbounded parameter ranges.
The general result follows from the proved finite-cycle reduction, not from
extrapolating the rectangle. Behavior after the first division is not classified.

## Documents

- [Detailed proofs](tex/ProfileDrop.tex).
- [Lean definitions and theorems](lean/ProfileDrop.lean).
- [Restricted prime-power affine-return helpers](lean/ProfilePrimePower.lean).
- [Bounded arithmetic certificate](go/ProfileDrop.go).
- [Exact-reference and boundary tests](go/ProfileDrop_test.go).

From the repository root:

```sh
lake env lean QCD.ProfileDrop.001/lean/ProfileDrop.lean
make go GOFILE=QCD.ProfileDrop.001/go/ProfileDrop.go
CGO_ENABLED=0 go test ./QCD.ProfileDrop.001/go
make tex TEXFILE=QCD.ProfileDrop.001/tex/ProfileDrop.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
