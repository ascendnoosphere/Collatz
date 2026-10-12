<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Arithmetic phase rigidity

Let \(q\) and \(c\) be odd positive integers. The base-two divided branches are
\[
F_0(x)=\frac{x}{2},\qquad F_1(x)=\frac{qx+c}{2}.
\]
The letter scale is \(a_0=1\) and \(a_1=q\). For an integer \(n\) of the letter's parity, the integer branch \(N_e(n)\) equals \(F_e(n)\).

If \(E<2/(q+2)\) and both a rational phase and its image lie at distance at most \(E\) from integers of the prescribed parities, then \(N_e(n)\) equals the next integer. If the carries vanish, the rational error is multiplied by \(a_e/2\) and no new error appears. Two solutions of \(D x=P x+A\) satisfy \((D-P)(x_1-x_2)=0\); when \(D\neq 0\) the difference is multiplied by \(P/D\), and when \(P\neq D\) the two solutions agree.

At \(q=3\) the threshold is \(2/5\). The odd letter meets the value \(1\) exactly at \(E=2/(q+2)\), so the congruence uses the strict inequality. For \(q=3\) and \(c=1\), \(N_1(1)=2\) and \(N_0(2)=1\).

## Statements

| Statement | Name |
| --- | --- |
| An odd positive integer is at least \(1\). | `PhaseRigidOddAtLeastOne` |
| If \(q\), \(c\), and \(n\) are odd, then \(qn+c\) is even. | `PhaseRigidOddNumeratorEven` |
| An even integer equals twice its quotient by \(2\). | `PhaseRigidEvenHalves` |
| The odd numerator equals twice its quotient by \(2\). | `PhaseRigidOddBranchExact` |
| The letter scale lies between \(0\) and \(q\). | `PhaseRigidLetterBounds` |
| The branch is \((a_e x+b_e)/2\). | `PhaseRigidShortcutSpec` |
| On a parity integer the rational branch equals integer division. | `PhaseRigidIntBranchCast` |
| \((q/2+1)\cdot 2/(q+2)=1\). | `PhaseRigidThresholdSaturates` |
| The even letter produces \(3/(q+2)\). | `PhaseRigidEvenAtThreshold` |
| For \(q\geq 1\), \(3/(q+2)\leq 1\). | `PhaseRigidEvenThresholdLeOne` |
| If \(0\leq a\leq q\) and \(E<2/(q+2)\), then \((a/2+1)E<1\). | `PhaseRigidScaleBelowOne` |
| The integer branch is then at distance less than \(1\) from the next integer. | `PhaseRigidDiscrepancyLtOne` |
| An integer of absolute value less than \(1\) is \(0\). | `PhaseRigidIntAbsLtOne` |
| A defect below \(2/(q+2)\) forces \(N_e(n)\) onto the next integer. | `PhaseRigidCongruence` |
| An exact integer step multiplies the rational error by \(a/2\). | `PhaseRigidErrorTransport` |
| \((D-P)(\xi-n)=0\) for two solutions of one affine equation. | `PhaseRigidFixedSubtract` |
| The difference is multiplied by \(P/D\) when \(D\neq 0\). | `PhaseRigidFixedRatio` |
| The two solutions agree when \(P\neq D\). | `PhaseRigidFixedUnique` |
| At \(q=3\) the threshold is \(2/5\). | `PhaseRigidClassicalFifth` |
| At \(q=3\), \(c=1\), the branches send \(1\) to \(2\) and \(2\) to \(1\). | `PhaseRigidClassicalLoop` |

## Reduction record

**Original obligation.** For odd positive integers \(q\) and \(c\), and for every phase of a base-two divided word with positive determinant, the distance to the prescribed positive parity integer is either zero or at least \(2/(q+2)\).

**Replacement obligations.** (i) The parity congruence that a legal integer has an integral divided branch. (ii) The strict estimate \((a/2+1)E<1\) whenever \(0\leq a\leq q\) and \(E<2/(q+2)\). (iii) The resulting equality of the integer branch with the next integer. (iv) Uniqueness for one affine fixed-point equation when the multiplier and the denominator differ.

**Recovery argument.** Suppose every phase lies at distance \(E<2/(q+2)\) from an integer of the prescribed parity. Then (ii) and (iii) make every integer carry vanish, so those integers follow the divided word. The rational phases and the integer phases then satisfy the same affine relation. If the word multiplier differs from the power of two in the denominator, (iv) forces each rational phase to equal the corresponding integer, and the defect is zero. The dichotomy is this implication together with the alternative that the defect is at least \(2/(q+2)\).

**Difficulty decrease.** The comparison no longer depends on a real-parameter family or on the length of the word. The remaining steps are one congruence modulo \(2\), one strict rational inequality, and one linear subtraction.

**Preservation conditions.** The integers \(q\) and \(c\) stay odd and positive, the base stays \(2\), and the defect bound stays strict. The distance bounds are hypotheses of the congruence: a nearest positive parity integer is not reconstructed. The odd letter saturates at equality, so the non-strict bound is not recovered. A defect of zero remains admissible.

## What is not claimed

The branches are not continued off the integers, and no smoothness or attraction statement is made. A phase defect of zero is not excluded. The non-strict bound \(E\leq 2/(q+2)\) is not claimed. The stronger uniform lower bound \(3/4\) is not claimed: the word \(1011100111110100\) has denominator \(2^{16}-3^{10}=6487\) and defect \(4858/6487\), which is at least \(2/5\) and strictly less than \(3/4\).

An integer check on odd multipliers and offsets at most \(15\), seeds at most \(40\), divided words of length at most \(4\) with multipliers in \(\{1,3,5\}\) and offsets in \(\{1,3,5\}\), and the single length-\(16\) word above, is not the uniform statement. No claim is made that every positive integer orbit reaches \(1\).
