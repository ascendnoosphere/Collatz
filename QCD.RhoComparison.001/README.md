<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Telescoping weights and mass-ratio bounds

For positive integer labels, define

```math
\rho(n)=\frac{1}{n(n+1)}\quad(n\ge1),\qquad
\mu(n)=\frac{2}{n(n-1)}\quad(n\ge2).
```

The two weights are positive on their stated domains. Their comparison is

```math
2\rho(n)\le\mu(n)\le4\rho(n)\qquad(n\ge3).
```

The upper bound is attained at $`n=3`$ and fails at $`n=2`$, where
$`4\rho(2)=2/3<1=\mu(2)`$. These are different weights, not identical laws.

[Detailed proofs](tex/RhoComparison.tex) ·
[Finite arithmetic proofs](lean/RhoComparison.lean) ·
[Infinite mass proofs](lean/RhoMass.lean) ·
[Exact finite certificate](go/RhoComparison.go) ·
[Reference tests](go/RhoComparison_test.go)

## Partial sums, tails, and windows

The identities

```math
\rho(n)=\frac1n-\frac1{n+1},\qquad
\mu(n)=\frac2{n-1}-\frac2n
```

hold for $`n\ge1`$ and $`n\ge2`$, respectively. Summing them gives

```math
\sum_{n=1}^{R}\rho(n)=\frac{R}{R+1},\qquad
1-\sum_{n=1}^{R}\rho(n)=\frac1{R+1}\qquad(R\ge0),
```

```math
\sum_{n=3}^{R}\mu(n)=1-\frac2R,\qquad
1-\sum_{n=3}^{R}\mu(n)=\frac2R\qquad(R\ge2).
```

Both formulas include the indicated empty sum. The second sum starts at $`3`$,
not $`2`$: the omitted weight is $`\mu(2)=1`$. Subtracting partial sums gives

```math
\sum_{n=R+1}^{N}\rho(n)=\frac1{R+1}-\frac1{N+1}\quad(0\le R\le N),
```

```math
\sum_{n=R+1}^{N}\mu(n)=\frac2R-\frac2N\quad(2\le R\le N).
```

## Infinite totals and label masses

The positive series converge, with

```math
\sum_{n=1}^{\infty}\rho(n)=1,\qquad
\sum_{n=3}^{\infty}\rho(n)=\frac13,\qquad
\sum_{n=3}^{\infty}\mu(n)=1.
```

Indeed, the partial sums above are bounded and their reciprocal remainders
tend to zero. Restricting either nonnegative series to any label set
$`S\subseteq\{3,4,\ldots\}`$ preserves summability, without a finiteness
assumption. If $`S`$ has a member, its mass is positive.

## Masses and their quotients

For $`n\ge3`$,

```math
\frac{\mu(n)}{\rho(n)}=\frac{2(n+1)}{n-1},\qquad
2\le\frac{2(n+1)}{n-1}\le4.
```

Multiplication by $`\rho(n)>0`$ gives the comparison. Thus every possibly infinite set
$`S\subseteq\{3,4,\ldots\}`$ satisfies

```math
2\sum_{n\in S}\rho(n)\le\sum_{n\in S}\mu(n)
\le4\sum_{n\in S}\rho(n).
```

Suppose $`c_\rho\ge0`$, $`u_\rho>0`$, and

```math
2c_\rho\le c_\mu\le4c_\rho,\qquad
2u_\rho\le u_\mu\le4u_\rho.
```

Then $`u_\mu>0`$ and

```math
\frac{c_\rho/u_\rho}{2}\le\frac{c_\mu}{u_\mu}
\le2\frac{c_\rho}{u_\rho}.
```

Indeed, the upper bound follows from
$`c_\mu/u_\mu\le4c_\rho/(2u_\rho)`$, and the lower bound from
$`2c_\rho/(4u_\rho)\le c_\mu/u_\mu`$.
For two possibly infinite label sets $`C,U\subseteq\{3,4,\ldots\}`$ with positive
$`\rho`$-mass on $`U`$, this applies to their respective masses. Disjointness
is not needed for the arithmetic comparison.

## Signed counterexamples

The weights $`+1`$ at $`3`$ and $`-1`$ at $`4`$ give

```math
4\bigl(\rho(3)-\rho(4)\bigr)=\frac2{15}
<\frac16=\mu(3)-\mu(4).
```

Swapping the signs refutes the lower bound:

```math
\mu(4)-\mu(3)=-\frac16
<-\frac1{15}=2\bigl(\rho(4)-\rho(3)\bigr).
```

## Finite certificate

The certificate checks five cleared comparison identities or inequalities for
$`3\le n\le4096`$, the $`\rho`$ telescope for $`1\le n\le4096`$, the $`\mu`$
telescope for $`2\le n\le4096`$, and 24 rational witnesses: partial sums
through $`8`$ including the empty cases, two windows, both endpoints, both
signed counterexamples, one finite mass comparison, and one quotient pair.
There are 28685 certificate checks.

The machine-integer predicates reject inputs outside their documented ranges;
all grid products are less than $`2^{38}`$. The rational helper is restricted to
the bounded witnesses, not arbitrary integer inputs. In these witnesses every
stored numerator and denominator has magnitude at most $`840`$; sums,
cross-products, and cross-cancelled products have magnitude below $`2^{21}`$.
The reference tests compare all seven grid truth values for $`2\le n\le4096`$
with exact `math/big.Rat` calculations, check every window with endpoints
through $`8`$, and reject always-true and always-false upper-bound predicates.
The certificate itself uses no heap allocation.

## Reduction record

- **Original obligation:** compare the two weights, their positive label
  masses, and quotients with positive denominator masses.
- **Replacement obligations:** the two reciprocal telescopes and the scalar
  identity $`\mu(n)/\rho(n)=2(n+1)/(n-1)`$.
- **Recovery:** telescope by induction, subtract to obtain windows, prove
  summability by bounded nonnegative partial sums, pass the finite bounds
  to the convergent restricted series, and compare the positive quotient
  denominators in their correct inequality directions.
- **Actual gain:** partial sums and windows have closed forms; the uniform
  termwise bounds reduce to $`2(n-1)\le2(n+1)\le4(n-1)`$.
- **Preserved conditions:** the comparison domain $`n\ge3`$, positive weights,
  nonnegative numerator masses, positive denominator masses, and the failure
  of the signed extensions.

The bounds do not assert that an orbit meets a target, nor that a sum of
capture fractions diverges. The finite certificate does not prove a statement
for every label. The Lean theorems prove the stated universal arithmetic
bounds, finite-sum formulas, and infinite-mass transfer independently of
that certificate.
