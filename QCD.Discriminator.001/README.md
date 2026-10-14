<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Neutral translations and return thresholds

Let $q\ge2$, $k\ge1$ and $t\ge1$ be integers. Set $D=q^k$ and $c=tD$, and
use the raw map

```math
C(x)=x/D\quad\text{when }D\mid x,\qquad
C(x)=qx+c\quad\text{when }D\nmid x.
```

Write $G_i(q)=1+q+\cdots+q^{i-1}$, with $G_0(q)=0$, and put

```math
b=tG_k(q),\qquad g=\gcd(q,t),\qquad
A=(q/g)b-t,\qquad N_0=\left\lfloor\frac{A}{q-1}\right\rfloor.
```

The multiplier need not be prime. The following separation holds for every
positive seed $n$ with $q\nmid n$.

## Escape class

If $g\nmid n$, every block consists of $k$ affine steps and one division:

```math
C^{s(k+1)+i}(n)=q^i(n+sb)+cG_i(q),
\qquad s\ge0,\quad 0\le i\le k.
```

In particular, at every raw time $\tau$,

```math
C^\tau(n)\ge n+b\left\lfloor\frac{\tau}{k+1}\right\rfloor.
```

Since $b\ge1$, the full raw orbit tends to infinity, not just a selected
subsequence of block landings.

## Return class

If $g\mid n$, there is a least delay $1\le s\le q/g-1$ for which
$m=n+sb$ is divisible by $q$. Let $j$ be the largest exponent at most $k$
with $q^j\mid m$. Then $1\le j\le k$, and the next division returns at

```math
J=m/q^j+tG_{k-j}(q),\qquad
C^{s(k+1)}(n)=m,\qquad
C^{s(k+1)+k-j+1}(n)=J.
```

The positive return obeys $qJ\le n+A$. Consequently,

- if $n>N_0$, then $J<n$;
- if $n\le N_0$, then $J\le N_0$.

These are comparisons for this return. A small return can change gcd class:
for $q=4$, $k=2$, $t=2$, the floor is $6$ and

```math
2\longmapsto40\longmapsto192\longmapsto12\longmapsto80\longmapsto5.
```

The returned seed $5$ is in the escape class, with subsequent block landings
$5+10s$. Thus a return below the floor need not produce a bounded orbit.

## Proofs and bounded implementation

- [Written proof](tex/Discriminator.tex): legal affine blocks, the least modular
  delay, the clipped division and both threshold inequalities.
- [Lean proof](lean/Discriminator.lean): the same separation, positivity of the
  return, the all-clock escape bound and the class-changing example. This module
  is included in the default build.
- [Go implementation](go/Discriminator.go) and [tests](go/Discriminator_test.go):
  independent raw replay and exact return comparisons.

The computational grid is $2\le q\le8$, $1\le k\le4$, $1\le t\le8$ and
$1\le n\le256$, excluding seeds divisible by $q$. It contains $43{,}328$
seeds: $13{,}440$ in the escape class and $29{,}888$ in the return class. Escape
checks include every partial state in nine blocks; return checks compare both
raw landings and both size inequalities. These finite checks complement the
unrestricted parameter proofs.

The implementation rejects unsupported parameters before starting a loop,
checks overflow, bounds raw replay by $64$ ticks and allocates no memory during
successful single-seed checks. The results concern the family $D=q^k$, $c=tD$
and the stated seed class.

Run from the repository root:

```sh
make lean
make go GOFILE=QCD.Discriminator.001/go/Discriminator.go
CGO_ENABLED=0 go test ./QCD.Discriminator.001/go
make tex TEXFILE=QCD.Discriminator.001/tex/Discriminator.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
