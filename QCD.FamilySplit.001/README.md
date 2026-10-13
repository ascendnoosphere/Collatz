SPDX-License-Identifier: CC-BY-4.0

# The even row of a local split

Let $T$ send an even natural number $n$ to $n/2$ and an odd natural number to $(3n+1)/2$. The even source word is the single letter $0$. The even parent word is empty. Evaluation applies the head letter first, and the empty word fixes its input.

## Statements

If $2$ divides $n$, then $2\cdot(n/2)=n$ and $T(n)=n/2$. The source word evaluates to $n/2$, and the empty parent word fixes $n/2$. This is the even doubling identity.

If $n>1$ is even and $p=n/2$, then $p$ is a positive integer, $p<n$, $T(n)=p$, and the source word on $n$ meets the parent word on $p$. This is the even family split.

If $n$ is odd, then $n$ is not a member of this row. In particular $3>1$ lies outside the row, and $2\cdot(3/2)=2\neq 3$.

## Reduction record

Original obligation: for each even integer $n>1$, exhibit a positive integer parent strictly smaller than $n$, reached by one even shortcut letter, with empty parent word.

Replacement obligation: the division identity $2\cdot(n/2)=n$ whenever $2$ divides $n$, together with the comparison of $n/2$ and $2\cdot(n/2)$.

Recovery argument: on an even input the shortcut is $n/2$ by definition, the one-letter word applies that same halving, and the empty word fixes the quotient. The two endpoints agree, so the quotient is the parent. Positivity of the quotient is the condition $n>1$, and strict decrease is $n/2<n/2+n/2$.

Difficulty decrease: the orbit is replaced by one division with remainder and one addition of a positive integer. Both are closed on the natural numbers. No search over later steps remains.

Preservation conditions: the hypotheses are $n>1$ and divisibility by $2$, and the conclusion is a positive strict parent together with agreement of the two words. Odd inputs are excluded rather than assigned this parent. No other local row is used.

## What is not claimed

The even row is not a cover of the integers greater than $1$. An input congruent to $2$ modulo $3$, an input congruent to $1$ modulo $4$, and an input $2^a u-1$ with $u$ odd are not given parents here. No complement of the even row is classified. No statement asserts that every integer greater than $1$ reaches $1$, or that a union of local rows contains every such integer.

The following are not proved: an affine lane decomposition; a residue order; a uniform contraction; a repunit divisor law; a reverse search bound; a profile drop; a neutral discriminator; phase rigidity of a continuization; a parent recursion beyond the one even letter; an excursion or cyclic gap; a terminal power; a marginal repair; and the comparison $2\rho\le\mu\le 4\rho$.

A finite integer check on the grid $\{1,2,\ldots,64\}$ counts exact instances of this row and of its complement inside that grid. The count is not the theorem.
