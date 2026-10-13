SPDX-License-Identifier: CC-BY-4.0

# Equal odd components

Let $a,b \ge 1$ and let $K = a + b$. A two-affine word is a pair of positive integers $n,y$ and a multiplier $q$ satisfying
$$
qn + 1 = 2^a y, \qquad qy + 1 = 2^b n.
$$
If $n = y$, then $a = b$, so $K$ is even, and the equation becomes $qn + 1 = 2^a n$. For $n > 0$ this is the cofactor identity
$$
(2^a - q)\, n = 1.
$$
Hence $n = 1$ and $q = 2^a - 1$. Both components are then the unit state. If $n \ge 3$ and $y \ge 3$, no such solution exists. The same conclusion holds when $K$ is assumed even at the outset: the half length equals both letters. If the common component is odd and the letter is positive, then $q$ is odd. If $K$ is odd, equal positive components are already impossible, because equality of the components forces the length to be even.

The bound $3$ is sharp on the equal-component locus. For every $t \ge 1$,
$$
q = 2^t - 1, \qquad n = y = 1, \qquad a = b = t
$$
satisfies both affine equations, $q$ is odd, and $K = 2t$. Equivalently,
$$
n\bigl(2^{2t} - q^2\bigr) = q + 2^t,
$$
and $2^{2t} - q^2 = (2^t - q)(2^t + q)$ whenever $q \le 2^t$.

## Reduction record

Original obligation: there is no two-affine solution whose two components are equal, of size at least $3$, when the length is even.

Replacement obligation: the single equation $qn + 1 = 2^a n$ in positive integers.

Recovery: $n = y$ substitutes into both affine equations, so the letters agree and the length is twice that letter. The even-length hypothesis then names the same half. The size bounds pass to the common state.

Difficulty decrease: the two affine equations become the natural-number factorization $(2^a - q)n = 1$, whose only positive solution is $n = 1$, $2^a = q + 1$.

Preservation: positive letters, the two affine equations, equality of the components, and the lower bound $3$. Oddness of the components is preserved and forces $q$ odd; it is not required for the size obstruction.

## What is not claimed

Unequal components $n \ne y$ are not excluded. A minimum-three theorem for every even length, covering unequal components, is a different statement and is not proved here. A positivity bound that treats every even-length cycle with a ratio at least $2$, rather than the case $n = y$, is not this cofactor identity. The comparison $2\rho \le \mu \le 4\rho$ is a different comparison and is not claimed. The finite integer checks elsewhere in this directory are checks on a bounded grid; they are not the theorem.
