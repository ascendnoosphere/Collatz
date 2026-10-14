<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Uniform return under a uniform hitting bound

Let $`q,c,d\in\mathbb{Z}`$ with $`\lvert d\rvert\ge 2`$. The offset sum satisfies $`U_0(q)=0`$ and $`U_{j+1}(q)=U_j(q)+q^j`$. The affine state is
```math
A_j(q,c,n)=q^j n+c\,U_j(q).
```
Time $`j`$ is a first hit of $`n`$ when $`d\mid A_j(q,c,n)`$ and $`d\nmid A_i(q,c,n)`$ for every natural number $`i<j`$.

The hypothesis that every seed hits means: for every $`n\in\mathbb{Z}`$ there exists a first hit. It is not proved. Divisibility of one integer is decidable, and the earlier-time clause at a fixed horizon is a finite conjunction, so a nonempty set of first hits has a least element $`j(n)`$. The total return is
```math
H(n)=A_{j(n)}(q,c,n)/d.
```

| # | Statement | Name |
| --- | --- | --- |
| .1 | $`A_0(q,c,n)=n`$. | AffineStateZero |
| .2 | No natural number is strictly less than zero. | NoEarlierAtZero |
| .3 | Time $`0`$ is a first hit if and only if $`d\mid n`$. | FirstHitZeroIff |
| .4 | If $`d\mid a`$, then $`\lvert d\rvert\cdot\lvert a/d\rvert=\lvert a\rvert`$. | NatAbsExactDiv |
| .5 | $`\lvert A_j(q,c,n)\rvert\le\lvert q\rvert^j\lvert n\rvert+\lvert c\rvert\lvert U_j(q)\rvert`$. | AffineTriangle |
| .6 | A seed has at most one first-hit time. | FirstHitUnique |
| .7 | The least hit is a first hit, and it is the only one. | LeastHitIsFirst, LeastHitOnly |
| .8 | A first hit obeys the triangle bound after exact division. | HitMagnitude |
| .9 | A slope bound and an offset bound add after multiplication by $`\lvert n\rvert`$. | AbsorbSlope |
| .10 | If every seed hits, $`A<\lvert d\rvert`$, and every least hit obeys $`\lvert q\rvert^{j(n)}\le A`$ and $`\lvert c\rvert\cdot\lvert U_{j(n)}(q)\rvert\le B`$, then $`\lvert d\rvert\cdot\lvert H(n)\rvert\le A\lvert n\rvert+B`$ for every $`n`$. | UniformReturnBound |
| .11 | The same hypotheses give entry into the radius $`\lfloor B/(\lvert d\rvert-A)\rfloor`$ and eventual periodicity of $`H`$. The cited core theorems ask exactly for $`A<m`$ and the bound at every integer, with $`m=\lvert d\rvert`$. | UniformReturnPeriodic |
| .12 | An admissible divisor does not divide $`1`$. | PureDivisionMissesOne |
| .13 | If $`d\mid n`$, time $`0`$ is the first hit and $`\lvert d\rvert\cdot\lvert n/d\rvert\le 1\cdot\lvert n\rvert+0`$, with $`1<\lvert d\rvert`$. The seed is this $`n`$, not every integer. | PureDivisionBound |
| .14 | On such an $`n`$, the least hit is $`0`$ and the time-zero quotient is $`n/d`$. | LeastHitOfDivisible, PureDivisionQuotient |
| .15 | For $`q=1`$, $`c=0`$, $`d=2`$, the seed $`1`$ is fixed at $`1`$ and never hits. | UnitFrozenState, UnitFrozenMisses, UnitFrozenNotEvery |
| .16 | For $`q=2`$, $`c=1`$, $`d=2`$, one has $`A_j(2,1,1)=2^{j+1}-1`$, which is never divisible by $`2`$. Thus $`\lvert q\rvert\ge 2`$ does not yield a hit of every seed. | TrapSumTwo, OddTranslationState, TwoNotDivPowSubOne, OddTranslationAvoids, OddTranslationNotEvery |
| .17 | If every least hit is at most $`J`$ and the largest $`\lvert q\rvert^{j}`$ for $`j\le J`$ is strictly less than $`\lvert d\rvert`$, that power and the largest offset on the same range give entry and eventual periodicity. When $`\lvert q\rvert\ge 1`$, the largest power is exactly $`\lvert q\rvert^{J}`$. | MaxPow, MaxOff, MaxPowLe, MaxOffLe, MaxPowOfPos, BoundedHitPeriodic |

## Reduction record

**ORIGINAL OBLIGATION.** From the hypothesis that every integer has a first hit, define the total return by the least such hit, and, from one pair $`A<\lvert d\rvert`$ and $`B`$ bounding $`\lvert q\rvert^{j}`$ and $`\lvert c\rvert\cdot\lvert U_j(q)\rvert`$ at every least hit, prove $`\lvert d\rvert\cdot\lvert H(n)\rvert\le A\lvert n\rvert+B`$ for every integer $`n`$, and deduce entry into the core radius together with eventual periodicity of $`H`$.

**REPLACEMENT OBLIGATIONS.** (i) Decide the first-hit predicate by divisibility of one integer and a finite earlier-time conjunction, then take the least hit by the least-element principle. (ii) Prove the absolute-value identity for an exact quotient and the triangle inequality for the affine state. (iii) Specialize both at the least hit and absorb the two uniform numerical bounds. (iv) Observe that the resulting estimate is the bound hypothesis of core entry and core periodicity at modulus $`\lvert d\rvert`$, and that $`A<\lvert d\rvert`$ is their gap hypothesis. (v) Separately, prove the slope-$`1`$, constant-$`0`$ comparison on seeds already divisible by $`d`$, and prove that this is not every seed. (vi) Prove two negative records: $`(q,c,d)=(1,0,2)`$ misses the seed $`1`$, and $`(2,1,2)`$ misses the seed $`1`$.

**RECOVERY ARGUMENT.** The total return is the quotient of the original affine state at the least time whose existence was assumed, so every value of $`H`$ is an exact division of a state already attached to the seed. The inequality of (iii) is the original absolute-value comparison, not a new norm. Core entry and core periodicity are applied to this same $`H`$, at $`m=\lvert d\rvert`$, with no change of quantifiers: $`A<m`$ and the bound at every integer are the hypotheses already proved. The pure-division statement recovers the same comparison only on the divisible seeds, and the failure at the seed $`1`$ is the obstruction to dropping the every-seed hypothesis.

**DIFFICULTY DECREASE.** An unbounded search for a hitting time is replaced, under the every-seed hypothesis, by one least natural number. The return bound is then one triangle inequality and one absorption, with no induction on the seed. Periodicity is not reproved: it is the already closed core argument applied to a map that now satisfies its hypotheses. The negative records are closed computations, the odd one being the identity $`A_j(2,1,1)=2^{j+1}-1`$.

**PRESERVATION CONDITIONS.** The every-seed hypothesis remains explicit and is not discharged. The pair $`(A,B)`$ is an additional hypothesis, uniform in the seed. Signs of $`q`$, $`c`$, $`d`$, and $`n`$ are unrestricted except for $`\lvert d\rvert\ge 2`$. The core theorems are instantiated only after $`H`$ has been defined on every integer. The pure-division theorem quantifies only over seeds divisible by $`d`$.

## Formal verification boundary

The active Lean declarations end with `NegTwoOneFirstTwoBefore`.
The subsequent large block beginning with `ZeroOffset` is an explicitly
**uncompiled historical appendix** inside a Lean block comment.
Names such as its second `UniformReturnBound` do not declare checked theorems
and do not replace the active `UniformReturnBound` listed above.
A build is not proof verification of that commented material. The appendix
is retained for provenance, not offered as a second formal implementation.

## What is not claimed

- That every seed hits, for a general record. A first hit by time $`J`$ on each residue $`0,\ldots,\lvert d\rvert-1`$ does lift to every integer, because a multiple of $`d`$ does not move the first hit.
- That the every-seed hypothesis alone produces one $`A<\lvert d\rvert`$ bounding $`\lvert q\rvert^{j(n)}`$ for every seed. That existence follows when every least hit is at most $`J`$ and the largest $`\lvert q\rvert^{j}`$ for $`j\le J`$ is strictly less than $`\lvert d\rvert`$. If $`\lvert q\rvert\ge 2`$ and every least hit satisfies $`\lvert q\rvert^{j(n)}<\lvert d\rvert`$, the times themselves are bounded by one such horizon, and the core conclusions follow. If instead $`\lvert q\rvert\ge\lvert d\rvert`$, the seed $`1`$ has no such small-slope hit. Without either a horizon or that small-slope hypothesis, the pair $`(A,B)`$ remains a hypothesis.
- That $`\lvert q\rvert\ge 2`$ produces a first hit of every seed, or a uniform slope below $`\lvert d\rvert`$. The residue walk $`r\mapsto qr+c`$ on $`\mathbb{Z}/\lvert d\rvert\mathbb{Z}`$ is the obstruction: a class that never meets $`0`$ has no first hit, and a class whose least hit satisfies $`\lvert q\rvert^j\ge\lvert d\rvert`$ forbids every candidate $`A<\lvert d\rvert`$. Neither alternative is removed by $`\lvert q\rvert\ge 2`$. For each residue class modulo $`\lvert d\rvert`$, exactly one of the following holds: the class has no first hit; or it has one common first-hit time $`j`$ with $`\lvert d\rvert\le\lvert q\rvert^{j}`$; or it has one common first-hit time $`j`$ with $`\lvert q\rvert^{j}<\lvert d\rvert`$. The instance $`q=2`$, $`c=1`$, $`d=2`$ is proved, and the odd class never meets $`0`$.
- That $`q=1`$, with an arbitrary offset and an arbitrary admissible divisor, makes every seed hit. The record $`q=1`$, $`c=0`$, $`d=2`$ misses the seed $`1`$. If instead $`\gcd(\lvert c\rvert,\lvert d\rvert)=1`$, every seed hits by time $`\lvert d\rvert`$, and the total return enters the core and is eventually periodic.
- Core entry, a core radius, or eventual periodicity for pure division on all of $`\mathbb{Z}`$. The comparison with slope $`1`$ and constant $`0`$ is proved only for seeds already divisible by $`d`$.
- Equality of $`H`$ with a return read off the raw step along a mixed orbit of divisions and affine steps.
- Periodicity of the raw step. The periodicity theorem is about iteration of $`H`$.
- Any statement about the classical Collatz map.
- That a finite count of hits for $`q=1`$, divisors $`\pm 2`$, and seeds $`-20,\ldots,20`$ proves a universal core, or proves that every integer hits.
