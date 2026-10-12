<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Division-free affine prefixes

Let \(q,c,d,n\in\mathbb{Z}\) with \(|d|\ge 2\), and let the raw step be
\[
T(n)=\begin{cases} n/d, & d\mid n,\\ qn+c, & d\nmid n.\end{cases}
\]
Write \(T^{0}(n)=n\) and \(T^{j+1}(n)=T(T^{j}(n))\). The offset sum is
\(U_{0}(q)=0\) and \(U_{j+1}(q)=U_{j}(q)+q^{j}\), equivalently
\(U_{j+1}(q)=q\,U_{j}(q)+1\). The affine state is
\[
A_{j}(q,c,n)=q^{j}n+c\,U_{j}(q).
\]
Time \(j\) is a first hit of \(n\) when \(d\mid A_{j}(q,c,n)\) and
\(d\nmid A_{i}(q,c,n)\) for every \(i<j\).

| # | Statement | Carried by |
| --- | --- | --- |
| .1 | **Raw prefix.** If \(d\nmid T^{i}(n)\) for every \(i<j\), then \(T^{j}(n)=A_{j}(q,c,n)\). The same equality holds at every \(k\le j\). | `PrefixAffine`, `RawPrefixEqAffine` |
| .2 | **Affine prefix.** If \(d\nmid A_{i}(q,c,n)\) for every \(i<j\), then \(T^{j}(n)=A_{j}(q,c,n)\). Thus \(T^{k}(n)=A_{k}(q,c,n)\) for every \(k\le j\). | `AffinePrefixRaw`, `AffinePrefixEqRaw` |
| .3 | **First hit.** Time \(j\) is a first hit of \(n\) if and only if \(d\mid T^{j}(n)\) and \(d\nmid T^{i}(n)\) for every \(i<j\). | `IsFirstHit`, `IsFirstHitIffRaw` |
| .4 | **Immediate quotient.** If \(j\) is a first hit of \(n\), then \(T^{j+1}(n)=A_{j}(q,c,n)/d\) and \(d\,T^{j+1}(n)=A_{j}(q,c,n)\). | `FirstHitQuotient`, `FirstHitReconstruction` |
| .5 | **One-hit majorant.** If \(j\) is a first hit of \(n\), then \(|d|\,|T^{j+1}(n)|\le |q|^{j}|n|+|c|\,|U_{j}(q)|\). Since \(|U_{j}(q)|\le \sum_{i<j}|q|^{i}\), the same successor also satisfies \(|d|\,|T^{j+1}(n)|\le |q|^{j}|n|+|c|\sum_{i<j}|q|^{i}\). | `FirstHitMagnitude`, `TrapSumNatAbsLe`, `FirstHitPowerMajorant` |

The inductive step at time \(j+1\) uses non-divisibility only at time \(j\). There the raw step is the affine branch, the inductive hypothesis replaces the raw state by \(A_{j}(q,c,n)\), and the offset recursion gives
\[
q\bigl(q^{j}n+c\,U_{j}(q)\bigr)+c=q^{j+1}n+c\,U_{j+1}(q).
\]
Time \(0\) is the seed on both sides. Divisibility at the time named by the conclusion is not forbidden: the guard quantifies only over earlier times.

## Reduction record

**ORIGINAL OBLIGATION.** For every parameter record, every integer seed, and every time \(j\), identify the raw iterate at time \(j\) with the affine state whenever \(d\) divides no earlier raw iterate, and recover the same identification from a division-free affine prefix.

**REPLACEMENT OBLIGATIONS.** (i) Define the affine state \(q^{j}n+c\,U_{j}(q)\). (ii) Prove the raw-prefix equality by induction on \(j\). (iii) Prove the affine-prefix equality by the same induction. (iv) Prove that the first time the affine state is divisible is exactly the first time the raw iterate is divisible.

**RECOVERY ARGUMENT.** Both sides are states of the original raw step at the original clock. The successor step applies the affine branch only after the guard has excluded division, then rewrites the offset by \(U_{j+1}(q)=q\,U_{j}(q)+1\). Restricting the guard from \(j\) to any \(k\le j\) recovers every earlier term of the prefix. When the state at time \(j\) is divisible, the equality at time \(j\) still holds and the induction is not applied at any later time.

**DIFFICULTY DECREASE.** A mixed word of divisions and affine branches, of unbounded dependence on the seed, is replaced on one finite prefix by a closed affine expression. The induction measure is the time \(j\), which drops to the base \(j=0\) in every branch. No residue search and no return exponent remain in the statement.

**PRESERVATION CONDITIONS.** The parameter record is unchanged: \(q\) and \(c\) are arbitrary integers and \(|d|\ge 2\), so negative multipliers, negative offsets, and negative divisors remain. The quantifiers are every record, every seed, and every time. The guard is non-divisibility at times \(i<j\), not at time \(j\). Equality is identity of integers, not congruence.

## What is not claimed

- The value of \(T^{m}(n)\) at any time \(m>j+1\) after a first hit at time \(j\), and every iterate after a division that is not that immediate quotient.
- Equality of \(T^{j+1}(n)\) with \(A_{j+1}(q,c,n)\).
- That \(d\) eventually divides some state of the orbit.
- Any bound on the first time at which \(d\) divides a state.
- A return past the immediate quotient, a block length, or a residue-dependent exponent.
- Any density of seeds, times, or residues.
- Convergence, divergence, or cycle structure of any classical Collatz orbit.
- That agreement on the finite set \(|q|\le 4\), \(|c|\le 4\), \(d\in\{\pm 2,\pm 3,\pm 5\}\), seeds \(-8,\ldots,8\), and times \(j\le 6\) proves the identity for every integer outside that set.
