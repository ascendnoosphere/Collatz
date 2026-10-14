<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Even division totals in a two-return cycle

For the raw map that halves an even positive integer and sends an odd integer
$x$ to $qx+1$, two successive odd returns in a cycle satisfy

```math
2^a y=qx+1,\qquad 2^b x=qy+1.
```

Here $q$ is odd, $x,y$ are positive odd integers, and $a,b$ count divisions.
The number of divisions is $K=a+b$, not the number of raw ticks.
The states may coincide.

## Product obstruction

**Theorem.** If $K$ is even and $x,y\ge2$, the two equations cannot both hold.
In fact, the algebraic result holds for every natural multiplier $q$ and all
natural $a,b$: no parity assumption on the multiplier or states is needed.

Write $K=2t$. Substitution gives

```math
2^{a+b}x=q^2x+q+2^a,
```

so $q^2<2^{2t}$ and hence $q\le2^t-1$. For any common lower bound
$x,y\ge\mu\ge2$, this implies

```math
\mu q+1\le\mu2^t-1,
\qquad
(\mu q+1)^2<\mu^2 2^{2t}.
```

On the other hand, the nonnegative slack identity

```math
\mu(qx+1)+(x-\mu)=(\mu q+1)x
```

and its counterpart at $y$ imply, after multiplication and cancellation of
$xy>0$,

```math
\mu^2 2^{a+b}\le(\mu q+1)^2.
```

These inequalities contradict each other. They apply uniformly to every
split $a+b=2t$, without an enumeration of states or multipliers.

The lower bound is sharp. At $q=3$, $x=y=1$, $a=b=2$, both equations hold
and $(q+1)^2=2^{a+b}=16$.

## Complementary factors

For natural $m,q$ with $q\le2^m$, put $u=2^m-q$, $v=2^m+q$. Then

```math
uv=2^{2m}-q^2,\qquad u+v=2^{m+1},\qquad v-u=2q.
```

Conversely, if $q^2\le2^{2m}$ and an ordered natural pair $u\le v$ has that
sum and product, it recovers the same multiplier: $v-u=2q$.
Zero factors and equal factors are included.

In particular, $2^{2m}-q^2=7$ has exactly one natural solution with
$q\le2^m$: $m=2$, $q=3$. Its complementary factors are $1$ and $7$.
This is the even-exponent case; odd division totals and cycles with more
than two odd returns are separate questions.

## Proofs and implementation

- [Written proofs](tex/ReverseBound.tex): closure, the product comparison,
  factor recovery, and the sharp boundary at state $1$.
- [Lean proofs](lean/ReverseBound.lean), in
  `GeneralizedCollatz.ReverseBound`: `EvenTotalNoCycle` proves the algebraic
  obstruction; `EvenLengthNoCycle` specialises it to an odd multiplier.
  `FactorRecovery` and `DeltaSevenOnly` prove the factor statements.
- [Go checks](go/ReverseBound.go) and [tests](go/ReverseBound_test.go): exact
  comparisons at ranks $1\le t,m\le12$, all multipliers through the relevant
  root, and minima $2\le\mu\le8$. The closure grid uses $0\le a,b\le4$,
  $0\le q\le8$, and $1\le x,y\le8$; only present equations count as
  verified closures. Arithmetic overflow is rejected, including wrapped
  exponents. The finite checks supplement the unrestricted proofs.

Run from the repository root:

```sh
make lean
make go GOFILE=QCD.ReverseBound.001/go/ReverseBound.go
PATH="$HOME/.local/go/bin:$PATH" CGO_ENABLED=0 go test ./QCD.ReverseBound.001/go
make tex TEXFILE=QCD.ReverseBound.001/tex/ReverseBound.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
