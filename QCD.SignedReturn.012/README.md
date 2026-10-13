<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Reflection at the negative unit multiplier

Let $`T_0(q)=0`$ and $`T_{j+1}(q)=T_j(q)+q^j`$. The affine state is
```math
A_j(q,c,n)=q^j n+c\,T_j(q).
```
A parameter record has multiplier $`q`$, offset $`c`$, and divisor $`d`$ with
$`|d|\ge 2`$, hence $`d\neq 0`$. The raw step divides by $`d`$ when $`d`$
divides the state and otherwise sends $`n`$ to $`qn+c`$. Time $`j`$ is a first
hit when $`d`$ divides $`A_j(q,c,n)`$ and divides $`A_i(q,c,n)`$ for no
$`i<j`$. An integer $`r`$ is a return of $`n`$ when some first hit has affine
state $`dr`$.

For every integer $`C`$, every integer $`n`$, and every natural number $`k`$,
```math
T_{2k}(-1)=0,\qquad T_{2k+1}(-1)=1,
```
and the powers are $`(-1)^{2k}=1`$ and $`(-1)^{2k+1}=-1`$. Therefore
```math
A_{2k}(-1,C,n)=n,\qquad A_{2k+1}(-1,C,n)=C-n.
```
The same closed form follows from the two-time repetition. For every time
$`j`$,
```math
A_{j+2}(-1,C,n)=A_j(-1,C,n),
```
because the two new offset powers $`(-1)^j`$ and $`(-1)^{j+1}`$ cancel and the
leading power is unchanged. The base cases are $`j=0`$ and $`j=1`$:
$`A_0(-1,C,n)=n`$ and $`A_1(-1,C,n)=C-n`$. By induction on $`k`$, time $`2k`$
repeats time $`0`$ and time $`2k+1`$ repeats time $`1`$, so every even time
equals $`n`$ and every odd time equals $`C-n`$. In particular
$`A_2(-1,C,n)=n`$ and $`A_3(-1,C,n)=C-n`$.

Now fix the multiplier $`-1`$, an admissible divisor $`d`$, and a seed $`n`$.

- The first hit is $`0`$ if and only if $`d`$ divides $`n`$. In that case
  $`n=d\cdot(n/d)`$, the raw step equals $`n/d`$, and no later time is a
  first hit. The return is $`n/d`$.
- If $`d`$ does not divide $`n`$ but $`d`$ divides $`C-n`$, the first hit is
  exactly $`1`$. The affine state there is $`C-n`$, the return is
  $`(C-n)/d`$, and the raw orbit takes one affine step to $`C-n`$ and then
  divides by $`d`$.
- If $`d`$ divides neither $`n`$ nor $`C-n`$, there is no first hit. Every
  even time repeats $`n`$ and every odd time repeats $`C-n`$. The raw orbit
  alternates between those two values and never divides.

A return exists if and only if $`d`$ divides $`n`$ or $`d`$ divides $`C-n`$.
A return therefore exists only in the first two clauses. The third clause is
a trap of the undivided branch, not a cycle of the return map: a return cycle
would require a return of $`n`$, and none exists.

## Reduction record

**ORIGINAL OBLIGATION.** For multiplier $`-1`$, every integer offset, every
integer seed, and every admissible divisor, evaluate the affine state at every
time and decide whether a first hit exists. When it exists, identify its time
and the integer return quotient. When it does not, show that the alternating
pair is not a cycle of the return map.

**REPLACEMENT OBLIGATIONS.** Prove $`(-1)^{2k}=1`$ and $`(-1)^{2k+1}=-1`$.
Combine those powers with $`T_{2k}(-1)=0`$ and $`T_{2k+1}(-1)=1`$. Prove the
two-step identity at every time, including the base times $`0`$ and $`1`$, and
propagate it by induction on the half-index. Split seeds into the three
divisibility clauses $`d\mid n`$, $`d\nmid n`$ but $`d\mid C-n`$, and neither.
In the third clause, identify the raw orbit with the same alternation.

**RECOVERY ARGUMENT.** The affine state is the original expression
$`q^j n+c\,T_j(q)`$ at $`q=-1`$. The return is the original integer quotient
by the record's divisor, using $`|d|\ge 2`$ so that $`d\neq 0`$. The time-zero
clause recovers the raw division branch. The time-one clause recovers one
affine raw step followed by that division. The third clause recovers every
raw iterate, because both residues miss $`d`$ and the raw step therefore stays
on the affine branch. No residue representative replaces the seed, and no
time is omitted from the parity split.

**DIFFICULTY DECREASE.** Before the evaluation, the obstruction is an infinite
family of affine values indexed by time. The two-step relation is well-founded
induction on the half-index $`k`$, with base cases $`k=0`$, namely times $`0`$
and $`1`$, and with every successor strictly closer to that base. After the
closed form, every time carries one of two integers, $`n`$ or $`C-n`$. The
first-hit search over $`\mathbb{N}`$ becomes two divisibility checks. No
unresolved child remains indexed by an arbitrary time.

**PRESERVATION CONDITIONS.** The multiplier is $`-1`$ because that is the
statement being proved, not an extra constraint placed on a general-multiplier
claim. The offset and the seed remain arbitrary integers, positive or
negative. The divisor remains an arbitrary integer with absolute value at
least $`2`$, so negative divisors stay. Both directions of the time-zero
characterization are proved. The third clause is not reclassified as a return.

## What is not claimed

- Any statement for a multiplier other than $`-1`$.
- The raw state at any time after the division in the first clause, or after
  the division in the second clause.
- That a first hit exists when $`d`$ divides neither $`n`$ nor $`C-n`$.
- That the alternating raw orbit is a cycle of the return map. It is a trap
  of the undivided branch.
- A bound on the absolute value of a return, a density of seeds, or any
  convergence statement for a classical Collatz orbit.
- That agreement of the three clauses on a finite set of offsets, seeds,
  times, and admissible divisors proves the identities for every integer
  outside that set.
