<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# First hits for multiplier two, offset one, and divisor three

The raw step divides a state by \(3\) when \(3\) divides the state, and otherwise sends \(n\) to \(2n+1\). The affine state at time \(j\) is \(A_j(n)=2^j n+T_j\), where \(T_0=0\) and \(T_{j+1}=2T_j+1\). A first hit is the least \(j\) such that \(3\) divides \(A_j(n)\). The return is the raw step applied to the raw iterate at that time.

## Statements

Seed \(1\) has first hit \(1\), affine state \(3\), and return \(1\).

Seed \(4\) has first hit \(1\), affine state \(9\), and return \(3\).

The residue step \(r\mapsto 2r+1\) on \(\mathbb{Z}/3\mathbb{Z}\) fixes the class of \(2\). Every residue iterate of seed \(2\) remains that class. Seed \(2\) therefore has no first hit, and \(3\) divides no state of its raw orbit.

It is not true that every integer has a first hit. Seed \(2\) is a witness.

If a seed \(n\) does have a first hit, and \(r\) is the return, then
\[
3\lvert r\rvert\le 2\lvert n\rvert+1.
\]
The proof is the residue classification. Remainder \(0\) hits at time \(0\) with return \(n/3\), and the numerator bound is \(\lvert n\rvert\le 2\lvert n\rvert+1\). Remainder \(1\) hits at time \(1\) with return \((2n+1)/3\), and the numerator bound is \(\lvert 2n+1\rvert\le 2\lvert n\rvert+1\). Remainder \(2\) has no first hit, so it is excluded from the inequality.

## Reduction record

**ORIGINAL OBLIGATION.** For multiplier \(2\), offset \(1\), and divisor \(3\), identify the first hit, the affine state, and the return of the seeds \(1\) and \(4\); show that seed \(2\) is fixed in residue and has no first hit; deduce that not every integer has a first hit; and prove \(3\lvert r\rvert\le 2\lvert n\rvert+1\) for every seed that does hit.

**REPLACEMENT OBLIGATIONS.** Prove that every integer has remainder \(0\), \(1\), or \(2\) modulo \(3\). For remainder \(0\), prove a first hit at time \(0\) with return \(n/3\). For remainder \(1\), prove a first hit at time \(1\) with affine state \(2n+1\) and return \((2n+1)/3\). For remainder \(2\), prove that the residue step fixes the class and that the raw orbit never divides. Prove the two numerator inequalities \(\lvert n\rvert\le 2\lvert n\rvert+1\) and \(\lvert 2n+1\rvert\le 2\lvert n\rvert+1\), and the cancellation \(3\lvert a/3\rvert=\lvert a\rvert\) when \(3\) divides \(a\).

**RECOVERY ARGUMENT.** The division identity \(n=3(n/3)+(n\bmod 3)\) makes the three remainders exhaustive. On a prefix with no earlier affine hit, the raw iterate equals the affine state, so the return is the quotient of that state. Uniqueness of the first-hit time identifies the return in the bound. Cancellation turns each numerator inequality into the return inequality. Seed \(2\) is one integer with no first-hit time, which is the negation of the claim that every integer has one.

**DIFFICULTY DECREASE.** The obligation no longer quantifies over an arbitrary time before knowing the residue. Each seed is settled by one remainder in a three-element set. The remaining arithmetic is the sign split of \(\lvert 2n+1\rvert\) and the congruence \(2\cdot 2+1\equiv 2\pmod 3\).

**PRESERVATION CONDITIONS.** The parameters remain multiplier \(2\), offset \(1\), and divisor \(3\). The seed stays an arbitrary integer, with no positivity, boundedness, or coprimality restriction. The return is the raw step at the first hit, not a later core representative. The inequality is stated only under the hypothesis that a first hit exists. The witness against a total first-hit law is the same seed \(2\) whose residue is fixed.

## What is not claimed

Not every integer has a first hit.

The raw orbit of seed \(2\) never meets a multiple of \(3\), so that orbit does not enter a core by division.

If the raw orbit meets \(1\) or meets \(-1\), the returns before that meeting form blocks of length one or two. Writing \(a_{0}\) and \(a_{1}\) for those counts,
\[
3^{a_{0}}4^{a_{1}}\le 3^{a_{1}}\lvert n\rvert.
\]
The length of the chain and the two block counts are the same for every minimal chain from that seed to that target. On \(3^{t}\) the chain to \(1\) has length \(t\), with \(a_{0}=t\) and \(a_{1}=0\). On \(4\cdot 3^{t}\) the chain to \(1\) has length \(t+2\), with \(a_{0}=t+1\) and \(a_{1}=1\). The first time the raw orbit equals the target is \(a_{0}+2a_{1}\). Thus \(3^{t}\) meets \(1\) at time \(t\), \(4\cdot 3^{t}\) meets \(1\) at time \(t+3\), and \(-3^{t}\) meets \(-1\) at time \(t\). Through time \(t\), the orbit of \(4\cdot 3^{t}\) is \(4\cdot 3^{t-j}\); the next three states are \(9\), \(3\), and \(1\). On \(-3^{t}\) the chain to \(-1\) has length \(t\), with \(a_{0}=t\) and \(a_{1}=0\). Equality holds if and only if \(n=3^{t}\), \(n=4\cdot 3^{t}\), or \(n=-3^{t}\) for some natural number \(t\). These three families are pairwise disjoint. The first two are exactly the seeds whose equality chain ends at \(1\). The third is exactly the seeds whose equality chain ends at \(-1\).

Every orbit either is eventually larger than every bound, or meets \(0\), \(1\), or \(-1\). In the second case every state has absolute value at most \(2\lvert n\rvert+1\). The bound is attained: the orbit of \(1\) contains \(3\). The coefficient \(2\) alone is not enough, since \(|3|>2|1|\).

The return inequality is not claimed for a seed that has no first hit.

The count inequality is not claimed for a seed whose raw orbit meets neither \(1\) nor \(-1\).

No parameter triple other than multiplier \(2\), offset \(1\), and divisor \(3\) is treated.

A finite range of seeds is not an argument for the statements above.
