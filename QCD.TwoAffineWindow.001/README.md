<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Two-affine window

For an odd integer $`K\ge 3`$ and an odd natural number $`q`$, the positivity
test is
```math
2^K\le\Bigl(q+\frac13\Bigr)^2.
```
No real square root is used, and no cycle is asserted.

## Statement

The rational comparison holds if and only if
```math
9\cdot 2^K\le(3q+1)^2.
```
The two sides are distinct, because the left side is divisible by $`3`$ and
the right side is congruent to $`1`$ modulo $`3`$. Consequently the inequality
is strict whenever it holds. Expanding the square gives
```math
(3q+1)^2=9q^2+6q+1.
```

Let $`m`$ be the greatest natural number with $`m^2\le 2^K`$. For odd
$`K\ge 3`$,
```math
m^2<2^K<(m+1)^2,
```
and $`m\ge 2`$. The odd candidate is $`m-1`$ when $`m`$ is even and is $`m`$
when $`m`$ is odd. That candidate $`q`$ is odd, satisfies $`q\ge 1`$, and is
the unique odd natural number in the bracket
```math
q^2<2^K<(q+2)^2.
```
If $`m`$ is even, the odd candidate fails $`9\cdot 2^K\le(3q+1)^2`$.

## Reduction record

ORIGINAL OBLIGATION. Decide the rational positivity test
$`2^K\le(q+1/3)^2`$ for odd $`K\ge 3`$ and odd $`q`$.

REPLACEMENT OBLIGATIONS. Decide the integer comparison
$`9\cdot 2^K\le(3q+1)^2`$, and identify the unique odd natural number whose
square lies strictly below $`2^K`$ while its translate by two lies strictly
above $`2^K`$.

RECOVERY ARGUMENT. The identity
```math
q+\frac13=\frac{3q+1}{3}
```
and the positivity of $`9=3^2`$ convert one comparison into the other for
every pair of natural numbers. Equality of the cleared sides is impossible, so
a true comparison is strict. The odd bracket is recovered from the integer
floor by keeping the floor when it is odd and passing to its predecessor when
it is even.

DIFFICULTY DECREASE. Denominators and real square roots are removed. The
remaining comparison is one inequality of natural numbers, together with a
finite parity distinction on the integer floor.

PRESERVATION CONDITIONS. The equivalence holds for every natural pair, hence
on the odd window $`K\ge 3`$ and odd $`q`$. Oddness of $`K`$ is used to keep
the floor square strictly below the power of two. The lower bound $`K\ge 3`$
keeps that floor at least $`2`$. No extra bound on $`q`$ is imposed.

## What is not claimed

The integer comparison does not produce a cycle. It does not prove a
contraction, a residue-critical bound, or the classical comparison of the two
growth constants. A finite grid of odd pairs can corroborate the arithmetic;
the grid is not the theorem. External existence or classification results are
not imported.
