# Closed form of the signed offset sum

SPDX-License-Identifier: CC-BY-4.0

For $`q\in\mathbb{Z}`$ and $`j\in\mathbb{N}`$, the offset sum is defined by $`U_0(q)=0`$ and $`U_{j+1}(q)=q\,U_j(q)+1`$. The affine state is $`A_j(q,c,n)=q^j n+c\,U_j(q)`$. A time is a first hit when the denominator divides that state and divides no earlier state. The first-hit predicate is defined only; it is not classified.

## Statements

If $`q\ge 2`$, then for every $`j\in\mathbb{N}`$
```math
(q-1)U_j(q)=q^j-1,
```
the integer $`q-1`$ divides $`q^j-1`$, the quotient $`(q^j-1)/(q-1)`$ is exact in $`\mathbb{Z}`$, $`U_j(q)`$ equals that quotient, and $`U_j(q)\ge 0`$. Consequently
```math
A_j(q,c,n)=q^j n+c\cdot\frac{q^j-1}{q-1}.
```

If $`|q|\ge 2`$, the same signed quotient is exact for every integer $`q`$, positive or negative:
```math
U_j(q)=\frac{q^j-1}{q-1}.
```
The denominator is nonzero because $`|q|\ge 2`$ excludes $`q=1`$.

If $`|q|\ge 2`$, then
```math
\bigl(|q|-1\bigr)\,\bigl|U_j(q)\bigr|\le |q|^j-1.
```
For $`q\ge 2`$ the two sides are equal. The factor on the left is $`|q|-1`$, not $`|q-1|`$.

At $`q=-2`$ and $`j=2`$, the recurrence gives $`U_2(-2)=-1`$. The signed quotient is $`(4-1)/(-3)=-1`$. The positive repunit is $`(4-1)/(2-1)=3`$, and $`|U_2(-2)|=1\neq 3`$. The absolute bound at this point is the strict inequality $`1\le 3`$.

For $`q\le -1`$, the sum is nonpositive at even times and positive at odd times. The absolute recurrence is therefore
```math
\begin{aligned}
j\text{ even}&\Longrightarrow \bigl|U_{j+1}(q)\bigr|=|q|\,\bigl|U_j(q)\bigr|+1,\\ j\text{ odd}&\Longrightarrow \bigl|U_{j+1}(q)\bigr|=|q|\,\bigl|U_j(q)\bigr|-1.
\end{aligned}
```
The bound for $`q\le -2`$ is the induction of this recurrence through the two natural-number steps $`ra+1`$ and $`ra-1`$.

## Reduction record

ORIGINAL OBLIGATION. Express the offset sum inside the affine state by an exact formula for multipliers at least $`2`$, and by a proved absolute estimate for every integer multiplier of absolute value at least $`2`$, without treating a negative multiplier as a positive repunit.

REPLACEMENT OBLIGATIONS. Prove $`(q-1)U_j(q)=q^j-1`$ and divide by the nonzero integer $`q-1`$. For $`q\ge 2`$, prove nonnegativity and transport the equality to absolute values. For $`q\le -2`$, prove the parity sign law, the two absolute steps, and the two natural-number inequalities that advance the bound from time $`j`$ to time $`j+1`$.

RECOVERY ARGUMENT. Division by $`q-1`$ returns $`U_j(q)`$ because Lemma multiplication is exactly that product. For $`q\ge 2`$, both $`q`$ and $`U_j(q)`$ are nonnegative, so absolute value does not change either side and the bound is equality. For $`q<0`$ with $`|q|\ge 2`$, every time is even or odd; the corresponding absolute step matches one of the two natural-number inequalities, and induction from the zero sum closes the bound. Substituting the positive quotient into $`A_j(q,c,n)`$ recovers the affine state for $`q\ge 2`$.

DIFFICULTY DECREASE. The positive case is one product identity and one exact division, with nonnegativity by a separate induction of length $`j`$. The negative case does not search for a closed absolute formula. Its induction measure is the time $`j`$, every successor is one of two arithmetic comparisons in $`\mathbb{N}`$, and the base time $`0`$ is the zero sum. No branch retains an unproved divisibility or an unproved sign.

PRESERVATION CONDITIONS. The multiplier remains an arbitrary integer and the time an arbitrary natural number. The exact nonnegative quotient assumes $`q\ge 2`$. The signed quotient and the absolute inequality assume $`|q|\ge 2`$. The sign law and the absolute steps assume $`q\le -1`$, which follows from $`q<0`$ and $`|q|\ge 2`$. No regularity, boundedness, or genericity hypothesis is added. The denominator $`q-1`$ is proved nonzero from $`|q|\ge 2`$ rather than assumed. The inequality uses truncated subtraction in $`\mathbb{N}`$ only through identities proved for that subtraction.

## What is not claimed

The equality $`(|q|-1)\,|U_j(q)|=|q|^j-1`$ is claimed only for $`q\ge 2`$. It is false at $`q=-2`$, $`j=2`$.

The formula $`|U_j(q)|=(|q|^j-1)/(|q|-1)`$ is not claimed for negative $`q`$. The signed quotient with denominator $`q-1`$ is claimed, and at $`q=-2`$ that denominator is $`-3`$.

First hits are not classified. No return time, no orbit, and no statement about the raw division step is proved.

A finite rectangle of multipliers and times can agree with these identities without proving them for every integer. The rectangle is a check, not a proof.
