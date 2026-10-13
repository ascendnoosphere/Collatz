<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Unit return at multiplier one

Let $`q,c,d,n`$ be integers with $`|d|\ge 2`$, and let $`j`$ be a natural
number. The offset sum is $`T_0(q)=0`$ and $`T_{j+1}(q)=T_j(q)+q^j`$. The
affine state is
```math
A_j(q,c,n)=q^j n+c\,T_j(q).
```
The raw step sends $`n`$ to $`n/d`$ when $`d`$ divides $`n`$, and to $`qn+c`$
otherwise. Write $`S^j(n)`$ for its $`j`$-fold iterate, with $`S^0(n)=n`$.
The time $`j`$ is a first hit of the seed $`n`$ when $`d`$ divides
$`A_j(q,c,n)`$ and $`d`$ divides $`A_i(q,c,n)`$ for no natural number $`i<j`$.

Assume $`q=1`$. The unit evaluation $`T_j(1)=j`$ gives, for every integer
offset $`c`$, every integer seed $`n`$, and every time $`j`$,
```math
A_j(1,c,n)=n+jc.
```
If $`d`$ divides no affine state before time $`j`$, the same closed form is
the raw iterate: $`S^j(n)=n+jc`$. Consequently, if $`j`$ is a first hit, then
$`d`$ divides $`n+jc`$, the raw state at time $`j`$ equals $`n+jc`$, and the
next raw step is the integer quotient
```math
S(S^j(n))=(n+jc)/d.
```
Writing $`r`$ for that quotient,
```math
|d|\cdot|r|\le |n|+j|c|.
```
The identity $`|d|\cdot|r|=|n+jc|`$ is exact cancellation, and the inequality
is the triangle inequality. Since $`|q|=1`$ and $`|d|\ge 2`$, one has
$`|q|<|d|`$ and
```math
|d|\cdot|r|\le |q|\cdot|n|+j|c|.
```
At the seed $`n`$, this is the core inequality with expansion $`A=1`$ and
additive term $`B=j|c|`$.

## Reduction record

**ORIGINAL OBLIGATION.** For a parameter record with multiplier $`1`$, every
integer seed, and every first-hit time $`j`$, identify the affine state,
identify the raw step immediately after that hit, and bound the absolute value
of the resulting quotient in the form of a core inequality at that seed.

**REPLACEMENT OBLIGATIONS.** Evaluate $`A_j(1,c,n)`$ as $`n+jc`$ by the unit
offset sum. Prove that a prefix whose affine states are not divisible before
time $`j`$ has raw iterate $`n+jc`$. Deduce that a first hit makes the next
raw step equal to $`(n+jc)/d`$. Cancel $`|d|`$ against that quotient and apply
the triangle inequality. Record that the resulting bound is the core
inequality with expansion $`|q|=1`$ and additive term $`j|c|`$, using
$`|d|\ge 2`$ only to obtain the strict comparison of those two coefficients.

**RECOVERY ARGUMENT.** The multiplier hypothesis $`q=1`$ is substituted into
the original raw step, whose non-division branch is then $`n\mapsto n+c`$.
The iterate at the hitting time is an iterate of that same raw step, and the
return is one further application of it, not a later orbit point. The
numerator $`n+jc`$ is the original affine state under $`q=1`$, so divisibility
by the original divisor is preserved. The core form is the same numerical
inequality with the coefficient $`|n|`$ rewritten as $`|q|\cdot|n|`$.

**DIFFICULTY DECREASE.** The offset sum at multiplier $`1`$ is no longer a
word of $`j`$ powers: the unit evaluation replaces it by the integer $`j`$.
The prefix induction decreases the time, with successor strictly smaller than
$`j+1`$ and with base $`j=0`$ equal to the seed. After that identification,
one divisibility witness cancels $`|d|`$ in $`\N`$, so the quotient does not
remain in the bound. The triangle inequality is a single estimate on the
cancelled numerator. No later return time and no search over residue classes
remain open in the statement.

**PRESERVATION CONDITIONS.** The hypothesis $`q=1`$ is stated explicitly and
is not treated as the general-multiplier case. The divisor remains an arbitrary
integer with $`|d|\ge 2`$, so negative divisors stay. Seeds and offsets remain
arbitrary integers, positive or negative. The first-hit hypothesis keeps the
failure of divisibility at every $`i<j`$, and the return statement does not
drop that quantifier. The additive term is $`j|c|`$ for the hitting time at
hand. It is not replaced by a bound independent of $`j`$.

## What is not claimed

- A first hit need not exist. The theorems are conditional on
  $`\operatorname{Hit}(p,n,j)`$, or, for the prefix, on non-divisibility
  before time $`j`$.
- The additive term $`B=j|c|`$ depends on $`j`$. It is not proved here that
  $`j\le |d|-1`$, and $`B`$ is not replaced by $`(|d|-1)|c|`$ or by any other
  uniform quantity.
- The core inequality is proved at the seed of the chosen hit, for the single
  return at that time. It is not proved at every integer, and it is not used
  to force entry into a finite invariant interval or eventual periodicity.
- No statement is proved for a multiplier other than $`1`$.
- The raw orbit after the division is not identified with an affine state.
- Agreement of the identities on a finite set of integers is not a proof for
  every integer. The proof is the argument above.
