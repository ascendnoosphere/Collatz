<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Initial odd-burst occupation

For the classical shortcut, an even state takes the branch $T(n)=n/2$ and
an odd state takes the branch $T(n)=(3n+1)/2$. All states and clocks below
are natural numbers.

## Exact burst coordinates

For an odd seed, write

```math
n+1=2^{A(n)}u(n),\qquad u(n)\text{ positive and odd}.
```

Thus $A(n)=v_2(n+1)\ge1$. For an even seed, set $A(n)=0$. The entire
initial burst has the closed form

```math
T^j(n)+1=3^j2^{A(n)-j}u(n),\qquad 0\le j\le A(n).
```

Every state at $j<A(n)$ is odd, and the state at $j=A(n)$ is even.
For example:

| Seed | Burst length | Odd cofactor | Prefix through the first even state |
| --- | --- | --- | --- |
| $3$ | $2$ | $1$ | $3\to5\to8$ |
| $5$ | $1$ | $3$ | $5\to8$ |
| $7$ | $3$ | $1$ | $7\to11\to17\to26$ |
| $15$ | $4$ | $1$ | $15\to23\to35\to53\to80$ |

## Uniform source-weighted bound

For odd seeds $n\ge3$, define

```math
\mu(n)=\frac{2}{n(n-1)},\qquad
O(n)=\sum_{j<A(n)}\sqrt{T^j(n)}.
```

For every integer $A\ge1$ and every finite set $S$ of odd seeds $n\ge3$
with $A(n)\ge A$,

```math
\sum_{n\in S}\mu(n)O(n)
\le\frac{2560}{27}\left(\frac7{16}\right)^A.
```

The nonnegative series over **all** such seeds converges and satisfies the
same bound. In particular, the full initial occupation obeys

```math
\sum_{\substack{n\ge3\\n\text{ odd}}}\mu(n)O(n)\le\frac{1120}{27}.
```

The proof retains the original weight of each seed. Its main estimates are

```math
\mu(n)O(n)<\frac{80}{3}\left(\frac7{16}\right)^{A(n)}
\frac1{u(n)\sqrt{u(n)}},\qquad
\sum_{u\in U}\frac1{u\sqrt u}\le2
```

for every finite set $U$ of positive odd integers. Injectivity of
$n\mapsto(A(n),u(n))$ and a geometric tail of ratio $7/16$ complete the
summation. The rational ratio comes from $\sqrt3/4<7/16$.

This estimate concerns only the **initial** odd run. It is not an estimate
for the transported weights at a later entrance to an odd run, and it does
not imply capture of an individual seed.

## Proofs and builds

- [Written proof](tex/OddBurst.tex): exact burst formula, one-source estimate,
  odd-cofactor telescope, finite-family bound, and convergent infinite series.
- [Lean proof](lean/OddBurst.lean): namespace
  `GeneralizedCollatz.OddBurst`; main declarations `OddBurstClosedForm`,
  `OneBurstMass`, `InitialOddBurstOccupation`, and `InitialOddBurstSeries`.
  The infinite-series theorem proves summability as well as the numerical bound.

From the repository root:

```sh
lake build OddBurst
make lean
make tex TEXFILE=QCD.OddBurst.001/tex/OddBurst.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
