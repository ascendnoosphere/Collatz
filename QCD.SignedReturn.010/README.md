<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Returns for a zero multiplier

Let $q,c,d,n\in\mathbb{Z}$ with $|d|\ge 2$, and let the raw step be
$$
T(x)=\begin{cases} x/d, & d\mid x,\\ qx+c, & d\nmid x.\end{cases}
$$
The offset sum is $U_0(q)=0$ and $U_{j+1}(q)=U_j(q)+q^j$. The affine state is
$$
A_j(q,c,n)=q^j n+c\,U_j(q).
$$
Time $j$ is a first hit of $n$ when $d\mid A_j(q,c,n)$ and $d\nmid A_i(q,c,n)$ for every natural number $i<j$. Assume $q=0$.

For every integer $C$ and every natural number $j\ge 1$,
$$
A_j(0,C,n)=C.
$$
The proof uses $U_{k+1}(0)=1$: writing $j=k+1$ gives $0^j n+C\cdot 1=C$. Time zero remains the seed, $A_0(0,C,n)=n$.

| # | Statement | Carried by |
| --- | --- | --- |
| .1 | **Positive times.** If $j\ge 1$, then $A_j(0,C,n)=C$. | `ZeroAffine`, using `TrapSumZero` |
| .2 | **Divisible seed.** If $d\mid n$, the first hit is time $0$, the raw return is $T(n)=n/d$, and no later time is a first hit. | `ZeroHitCases`, first clause |
| .3 | **Divisible offset.** If $d\nmid n$ and $d\mid c$, the first hit is time $1$, the raw return is $T(T(n))=c/d$, and no other time is a first hit. | `ZeroHitCases`, second clause |
| .4 | **Double miss.** If $d$ divides neither $n$ nor $c$, then $A_0(n)=n$ and $A_j(n)=c$ for every $j\ge 1$. Both values are indivisible, so no time is a first hit. | `ZeroHitCases`, third clause |

The third clause assigns no return. Reaching the constant $c$ and staying there is a trap, not a division of the affine state.

When both $d\mid n$ and $d\mid c$, the first clause applies and the second does not. The return is $n/d$. The later value $c$ is not a first hit, because time zero already divided.

## Reduction record

**ORIGINAL OBLIGATION.** For every parameter record with multiplier $0$, every integer offset, every admissible divisor, and every integer seed, identify the first time at which the divisor meets the affine state, and identify the raw integer obtained by dividing that state, or prove that no such time exists.

**REPLACEMENT OBLIGATIONS.** Prove $A_j(0,C,n)=C$ for every $j\ge 1$, from $U_{k+1}(0)=1$. Prove that $d\mid n$ forces first hit $0$ and raw return $n/d$. Prove that $d\nmid n$ together with $d\mid c$ forces first hit $1$ and raw return $c/d$. Prove that if $d$ divides neither integer, then time $0$ equals $n$, every positive time equals $c$, and neither value is divisible, so no time is a first hit.

**RECOVERY ARGUMENT.** The three divisibility hypotheses exhaust the pairs $(d\mid n,\ d\mid c)$, with the overlap $d\mid n$ and $d\mid c$ retained in the first clause only. Time zero of the affine state is the original seed, so divisibility there is the original raw guard and the return $n/d$ is one raw step. At time one the state is the original offset, the preceding raw step is the affine branch $0\cdot n+c=c$, and the return $c/d$ is the next raw step. A later time cannot be first once time zero or time one has divided. In the double miss, both observed values fail the guard, so the original first-hit quantifier over $\mathbb{N}$ is empty and no quotient is formed.

**DIFFICULTY DECREASE.** Before the evaluation, a first hit is an unknown index $j\in\mathbb{N}$. The identity $A_j(0,C,n)=C$ for $j\ge 1$ collapses every positive time to one integer. The remaining comparisons are the two divisibility tests $d\mid n$ and $d\mid c$. The decreasing resource is the set of unchecked times: it falls from $\mathbb{N}$ to the empty set in every branch. There is no residual child indexed by $j\ge 2$.

**PRESERVATION CONDITIONS.** The multiplier is the stated value $0$, not a further specialization inside the proof. The offset and the seed remain arbitrary integers. The divisor remains an arbitrary integer $d$ with $|d|\ge 2$, so negative divisors and negative seeds stay in the statement. Both directions of each case are the divisibility hypothesis and the matching first-hit conclusion. The double miss keeps the original affine state and concludes that the first-hit predicate is false; it does not replace the seed by a fixed point or name a return.

## What is not claimed

- Any first hit, return, or affine evaluation for a multiplier other than $0$.
- A return in the case where $d$ divides neither the seed nor the offset. The constant value $c$ is not a return, and neither is the seed.
- That $c/d$ is the return when $d$ already divides the seed. That overlap returns $n/d$ at time zero.
- The raw orbit at any time after the single return step $n/d$ or $c/d$.
- Existence of a cycle for a general multiplier, a density of seeds or times, a core bound, or convergence of a classical Collatz orbit.
- That agreement on a finite set of divisors, offsets, and seeds proves the same trichotomy for every integer outside that set. The proof is the case split above.
