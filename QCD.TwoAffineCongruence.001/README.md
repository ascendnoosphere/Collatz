<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Two-affine congruence

Let $K$ and $a$ be nonnegative integers and let $q$ be an integer. Write
$$
\Delta=2^{K}-q^{2}.
$$
The first numerator is $q+2^{a}$ and, when $a\le K$, the partner numerator is $q+2^{K-a}$.

## Statements

$\Delta$ divides $q+2^{a}$ if and only if $2^{a}\equiv -q\pmod{\Delta}$. This equivalence does not use the sign or the parity of $\Delta$.

If $\Delta$ is odd, then $\gcd(\Delta,q)=1$. Every natural common divisor of $\Delta$ and $q$ divides $2^{K}$ and is odd, hence equals $1$.

If $\Delta$ is odd and $a\le K$, divisibility of $q+2^{a}$ implies divisibility of $q+2^{K-a}$. The identity is
$$
q\bigl(q+2^{K-a}\bigr)=2^{K-a}\bigl(q+2^{a}\bigr)-\Delta.
$$
Euclid's lemma then cancels the factor $q$.

If moreover $a<K$ and $y$ is the integer quotient of the partner numerator by $\Delta$, then $y$ is odd. Indeed $K\ge 1$, so $q$ is odd, the remaining power of two is even, and an odd product of the odd denominator with $y$ forces $y$ itself to be odd.

If $0<\Delta$, $a\le K$, and both numerators equal $n\Delta$ and $y\Delta$, then
$$
qn+1=2^{a}y,\qquad qy+1=2^{K-a}n.
$$
When $n$ and $y$ are odd, both seeds $qn+1$ and $qy+1$ are even if and only if $1\le a<K$.

If those quotient equations hold and $n=y$, then
$$
K=2a,\qquad q=2^{a}-1,\qquad n=y=1.
$$
Thus equal quotients are impossible when $K$ is odd. They are not impossible for even $K$: the lane $K=4$, $q=3$, $a=2$ has $\Delta=7$ and $n=y=1$.

The quotient at a zero exponent need not be odd. For $K=1$, $q=1$, and $a=1$, one has $\Delta=1$ and partner quotient $2$.

## Reduction record

**ORIGINAL OBLIGATION.** For positive odd $\Delta=2^{K}-q^{2}$, prove that $n=(q+2^{a})/\Delta$ is an integer if and only if $2^{a}\equiv -q\pmod{\Delta}$, that the partner $y=(q+2^{K-a})/\Delta$ is then an odd integer, and decide for which $K$ the equality $n=y$ can hold.

**REPLACEMENT OBLIGATIONS.** Replace the integrality claim by the divisibility form of the displayed congruence. Prove $\gcd(\Delta,q)=1$ from oddness of $\Delta$. Transfer divisibility from exponent $a$ to exponent $K-a$ by the square relation $2^{K}\equiv q^{2}\pmod{\Delta}$ and Euclid's lemma, assuming $a\le K$. Prove oddness of the partner quotient when $a<K$. Cancel $\Delta$ in the two quotient equations to obtain the product identities, and read the condition $1\le a<K$ off the parity of the seeds when both cofactors are odd. Classify $n=y$ by equating the numerators, using injectivity of $k\mapsto 2^{k}$, and factoring $\Delta=(2^{a}-q)(2^{a}+q)$.

**RECOVERY ARGUMENT.** The congruence is exactly divisibility of $q+2^{a}$, so it is the integrality of $n$. Coprimeness returns integrality of $y$ from integrality of $n$. The parity argument returns oddness of that quotient when $a<K$. Cancellation of the nonzero denominator returns the two product identities, and oddness of the cofactors returns the exact range of the exponents. Equality of the quotients forces $K=2a$ and reduces the cofactor $2^{a}-q$ to $\pm 1$; positivity of $\Delta$ excludes $-1$ and leaves only $q=2^{a}-1$ and $n=y=1$. An odd $K$ cannot equal $2a$.

**DIFFICULTY DECREASE.** Each replacement is one divisibility, one cancellation, or a split into the two signs of a cofactor of absolute value $1$. There is no search through a general exponential equation and no finiteness theorem for a generalized superelliptic equation. The equality case is one explicit triple.

**PRESERVATION CONDITIONS.** The denominator remains $2^{K}-q^{2}$, and the numerators remain $q+2^{a}$ and $q+2^{K-a}$. No lower bound $n,y\ge 3$ is added. Oddness of $\Delta$ is used for coprimeness and for the parity of $y$; it is not used as a substitute for positivity. Positivity is an explicit hypothesis of the equality classification. The zero-exponent boundary is excluded from the oddness statement rather than absorbed into it.

## What is not claimed

It is not claimed that $n=y$ is impossible whenever $K$ is even. The unit seed $K=2a$, $q=2^{a}-1$, $n=y=1$ is an equality, and $K$ is even.

It is not claimed that no even length admits a quotient of absolute value at least $3$. No bound of Nagell, Beukers, Le, or Bauer–Bennett is used.

Oddness of the partner uses $a<K$. It fails for $K=1$, $q=1$, $a=1$, where the partner quotient is $2$.

Nothing here concerns residue order, repunit divisors, profile drop, discriminators, phase rigidity, a parent identity, a family split, excursions, cyclic gaps, a terminal power, a marginal repair, or the comparison $2\rho\le\mu\le 4\rho$.

A finite grid of lanes, including lanes that fail the congruence and the even partner $2$, is not the theorem.
