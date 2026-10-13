<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Exact product of a signed division

Let $`d,a\in\mathbb{Z}`$. Write $`d\mid a`$ when $`a=dk`$ for some
$`k\in\mathbb{Z}`$. For $`d\neq 0`$, let $`a/d`$ be the truncating quotient.
The offset sum is $`T_0(q)=0`$ and $`T_{j+1}(q)=T_j(q)+q^j`$, and the affine
state is
```math
A_j(q,c,n)=q^j n+c\,T_j(q).
```
A parameter record has integers $`q`$, $`c`$, and $`d`$ with $`|d|\ge 2`$.
The time $`j`$ is a first hit of the seed $`n`$ when $`d`$ divides
$`A_j(q,c,n)`$ and $`d`$ divides $`A_i(q,c,n)`$ for no natural number $`i<j`$.

If $`d\neq 0`$ and $`d\mid a`$, then
```math
d\cdot(a/d)=a.
```
The same equality holds when $`a`$ is the affine state at a first hit. In
that case $`d\neq 0`$ because $`|d|\ge 2`$. The witness $`k`$ with $`a=dk`$ is
the quotient $`a/d`$, including when $`d`$ is negative.

If $`d\neq 0`$ and $`d\mid a`$, then
```math
|d|\cdot|a/d|=|a|.
```
The same equality holds for the affine state at a first hit. The absolute
value of a product is the product of the absolute values, in all four sign
patterns, so a negative divisor is not an exception. Both displayed formulae
are equalities. They do not drop a nonnegative remainder, and they are not
instances of the triangle inequality.

## Reduction record

**ORIGINAL OBLIGATION.** When a signed divisor divides an integer state,
recover that state from the truncating quotient by multiplication, as an
equality of integers and as an equality of absolute values, and obtain the
same two equalities when the state is the affine state at a first hit.

**REPLACEMENT OBLIGATIONS.** From $`d\neq 0`$ and a witness $`a=dk`$, prove
that the truncating quotient equals $`k`$, by the remainder constraint
$`|r|<|d|`$. Conclude $`d\cdot(a/d)=a`$. Prove $`|dk|=|d|\cdot|k|`$ by the
four sign patterns, including zero, and conclude
$`|d|\cdot|a/d|=|a|`$. Specialize $`a`$ to $`A_j(q,c,n)`$ under the first-hit
hypothesis, using $`|d|\ge 2`$ to obtain $`d\neq 0`$.

**RECOVERY ARGUMENT.** The witness equation $`a=dk`$ is an equality in
$`\mathbb{Z}`$. After the quotient is identified with $`k`$, multiplication
by $`d`$ is the same equation read in the reverse order, so the original
state is restored exactly. At a first hit the integer $`a`$ is the original
affine state of the original parameter record, so both equalities are
statements about that state. The absolute-value equality restores $`|a|`$,
not a larger integer, because no positive slack is added.

**DIFFICULTY DECREASE.** The decreasing resource is the number of uncancelled
factors in the witness equation $`a=dk`$. There is one factor, $`d`$. The
hypothesis $`d\neq 0`$ cancels it and replaces the existential witness by the
value of the quotient. The absolute-value step is a finite case split on the
signs of $`d`$ and $`k`$, and each case is an equality, so it adds no
remainder child. The first-hit specialization does not induct on the time
$`j`$. No unresolved child remains.

**PRESERVATION CONDITIONS.** The product theorems quantify over every integer
$`d\neq 0`$ and every integer $`a`$ divisible by $`d`$, with no positivity
restriction. The first-hit theorems keep the original parameter record,
including every divisor with $`|d|\ge 2`$, every integer seed, and every
time. The conclusion is equality in $`\mathbb{Z}`$ or in the natural numbers,
not congruence and not an inequality. The earlier-time failures stay in the
first-hit hypothesis; the cancellation itself uses divisibility at time $`j`$.

## What is not claimed

- A first hit need not exist for a given seed.
- Nothing is asserted about the raw orbit at any time after the first hit.
- A nonzero remainder is not replaced by a rounded quotient. If $`d`$ does
  not divide $`a`$, the product identities are not claimed.
- Division by zero is excluded. The hypothesis $`d\neq 0`$ is required for
  the quotient, and a parameter record also satisfies $`|d|\ge 2`$.
- The identity $`|d|\cdot|a/d|=|a|`$ is not the triangle inequality and is
  not obtained by discarding a nonnegative defect.
- No density, trap classification, core bound, or classical convergence
  statement is proved.
- Agreement of the two equalities for all nonzero $`d`$ with $`|d|\le 12`$ and
  all $`a`$ with $`|a|\le 36`$, together with the rejection of a
  non-multiple such as $`(d,a)=(4,6)`$ or $`(-5,7)`$, does not prove the
  identities for every integer outside that set.
