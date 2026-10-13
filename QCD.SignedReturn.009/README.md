<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Immediate return at exponent zero

Let $q,c,d,n\in\mathbb{Z}$ with $|d|\ge 2$, and let the raw step be
$$
T(n)=\begin{cases} n/d, & d\mid n,\\ qn+c, & d\nmid n.\end{cases}
$$
The offset sum satisfies $U_0(q)=0$. The affine state is
$$
A_j(q,c,n)=q^{j}n+c\,U_j(q).
$$
Time $j$ is a first hit of the seed $n$ when $d\mid A_j(q,c,n)$ and
$d\nmid A_i(q,c,n)$ for every natural number $i<j$. The second clause is
the bounded quantifier $\forall i\,(i<j\rightarrow d\nmid A_i(q,c,n))$.

| # | Statement | Carried by |
| --- | --- | --- |
| .1 | For every $q,c,n$, the time-zero state is the seed: $A_0(q,c,n)=n$. | `AffineStateZero` |
| .2 | For every predicate $P$ on $\mathbb{N}$, $\forall i\,(i<0\rightarrow P(i))$. The range is empty, so the implication is true because $i<0$ is false. | `NoEarlierTimeAtZero` |
| .3 | **First hit at zero.** $\operatorname{Hit}(p,n,0)$ if and only if $d\mid n$. | `FirstHitZeroIff` |
| .4 | **Immediate quotient.** If $d\mid n$, then $T(n)=n/d$ and $\lvert d\rvert\cdot\lvert n/d\rvert=\lvert n\rvert$. | `ImmediateQuotient` |
| .5 | **Core bound at exponent zero.** If $d\mid n$, $A=1$, and $B=0$, then $A<\lvert d\rvert$ and $\lvert d\rvert\cdot\lvert n/d\rvert\le A\lvert n\rvert+B$. The strict inequality uses $\lvert d\rvert\ge 2$. | `ImmediateCore` |

## Reduction record

**ORIGINAL OBLIGATION.** For every parameter record and every integer seed, identify a first hit at time zero with divisibility of the seed by the signed divisor, and, on that event, show that the raw division step obeys the core comparison with slope $1$ and constant $0$.

**REPLACEMENT OBLIGATIONS.** (i) Prove $A_0(q,c,n)=n$ from $q^0=1$ and the empty offset sum. (ii) Prove the bounded quantifier over $i<0$ from its definition as $\forall i\,(i<0\rightarrow P(i))$ and from the emptiness of that initial segment. (iii) Conclude the equivalence for a first hit at time zero, in both directions, retaining the earlier-time conjunct. (iv) From $d\mid n$, identify the raw step with $n/d$ and prove $\lvert d\rvert\cdot\lvert n/d\rvert=\lvert n\rvert$. (v) From $\lvert d\rvert\ge 2$, deduce $1<\lvert d\rvert$, and from the equality deduce the core inequality with $A=1$ and $B=0$.

**RECOVERY ARGUMENT.** Lemma (i) identifies the time-zero affine state with the original seed, so divisibility is the divisibility hypothesis of the original raw step. The return value is that raw step on its division branch, not a residue representative and not an affine iterate. The absolute-value identity is equality in $\mathbb{N}$ of the original absolute values. Specializing the core comparison to $A=1$ and $B=0$ restores the stated bound for this return and no other.

**DIFFICULTY DECREASE.** A first-hit search is indexed by an arbitrary time. At exponent zero the index is fixed, the offset sum is empty, and the earlier-time quantifier has empty domain, so that quantifier contributes no inductive child. The decreasing resource is the exponent, which is already zero. Absolute-value cancellation is one application of multiplicativity after the division identity $d\cdot(n/d)=n$.

**PRESERVATION CONDITIONS.** The quantifiers are every parameter record with $\lvert d\rvert\ge 2$ and every integer seed. The multiplier and the offset remain arbitrary integers, including negative values and zero; they do not appear in the time-zero state. Both directions of the first-hit equivalence are proved. The core inequality uses the same absolute values as the comparison $\lvert d\rvert\cdot\lvert n/d\rvert\le A\lvert n\rvert+B$. No positivity restriction is imposed on the seed.

## What is not claimed

- Existence of a first hit at any positive time.
- Any return after one or more affine steps, any block length, or any residue-dependent exponent.
- The core comparison with slope $1$ and constant $0$ for any map other than $n\mapsto n/d$ on integers already divisible by $d$.
- A core radius, entry into a finite interval, or eventual periodicity.
- Equality of a raw iterate with the affine state at any positive time.
- That $d$ eventually divides the orbit of every seed.
- Convergence, divergence, or cycle structure of any classical Collatz orbit.
- That agreement on the finite set of seeds $-30,\ldots,30$ and divisors $\pm 2,\pm 3,\pm 5$ proves the statements for every integer outside that set.
