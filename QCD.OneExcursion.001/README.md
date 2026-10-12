SPDX-License-Identifier: CC-BY-4.0

# One-excursion cover

Let \(n=2^a u-1\) with \(u\) odd and positive, and write \(T\) for the shortcut that sends an even integer to its half and an odd integer to \((3n+1)/2\). After \(a\) odd shortcuts the state is \(3^a u-1\). If \(3^a u\equiv 3\pmod{4}\), one further halving is exact and the exit is
\[
y=\frac{3^a u-1}{2}.
\]
The quarter parent \((3^{a+1}u-1)/8\) and the half parent \((3^a u-3)/4\) are the two elementary ways of clearing that exit back toward \(n\).

## Statements

The signed coefficients are
\[
C_1(a)=2^{a+3}-3^{a+1},\qquad C_2(a)=2^{a+2}-3^a.
\]
They satisfy \(C_1(a)=C_2(a+1)\) and \(C_2(a+1)=2C_2(a)-3^a\). Consequently \(C_1(a)>0\) if and only if \(a\le 2\), and \(C_2(a)>0\) if and only if \(a\le 3\). Both are negative for every \(a\ge 4\).

Assume \(u>0\) and \(2^a u\ge 1\). Then
\[
3^{a+1}u-1<8(2^a u-1)\iff 7<C_1(a)\,u.
\]
Assume in addition \(3\le 3^a u\). Then
\[
3^a u-3<4(2^a u-1)\iff 1<C_2(a)\,u.
\]
Thus, whenever the corresponding denominator divides the numerator, the quarter parent lies strictly below \(n\) precisely under the first inequality, and the half parent lies strictly below \(n\) precisely under the second. For \(a=2\) and \(u\ge 3\) both inequalities hold. For \(a=3\) and \(u>0\) the first fails and the second holds. For \(a\ge 4\) and \(u>0\) both fail.

For \(a\ge 2\) the gap \(4\cdot 3^a-9\cdot 2^a\) is nonnegative. If \(u\) is odd, then \(2\) divides \(3^a u-1\) and
\[
9(2^a u-1)+u(4\cdot 3^a-9\cdot 2^a)+5=8y.
\]
The middle summand is nonnegative, so \(9(n+1)\le 8(y+1)\). Along any chain of such steps,
\[
9^k(x_0+1)\le 8^k(x_k+1).
\]
Since \(9^6=531441\ge 524288=2\cdot 8^6\), an exit obeying the sixth-power bound is at least \(2n+1\). In that range none of
\[
3y+1<4n,\qquad y-1<2n,\qquad 2y-1<3n,\qquad y<2n
\]
holds. The fifth power does not give the same uniform cutoff: \(9^5=59049<65536=2\cdot 8^5\).

The same arithmetic identifies the forward orbit. For \(j\le a\),
\[
T^j(2^a u-1)=3^j 2^{a-j}u-1,
\]
and the congruence \(3^a u\equiv 3\pmod{4}\) makes \(T^{a+1}(n)=y\). If instead \(u\equiv(-1)^a\pmod{4}\), the two-even words meet: \(T^{a+2}(2^a u-1)\) and \(T^{a+1}(2^{a-1}u-1)\) both equal \((3^a u-1)/4\). A factorization \(3^a u=3^{a'}u'\) with \(3\nmid u\) and \(3\nmid u'\) has \(a=a'\) and \(u=u'\). The seed \(75=2^2\cdot 19-1\) exits at \(85\) and meets the quarter parent \(64<75\).

## Reduction

Original obligation: for one odd seed and its single-even exit, decide whether a cleared parent of the exit lies strictly below the seed.

Replacement obligations: the two coefficient comparisons above, and the shifted inequality \(9(n+1)\le 8(y+1)\) when \(a\ge 2\) and \(u\) is odd.

Recovery: each parent comparison is the corresponding coefficient inequality together with exact division by \(8\) or by \(4\). Six shifted steps and the numerical inequality \(9^6\ge 2\cdot 8^6\) force the exit to be at least \(2n+1\), which falsifies all four elementary strict inequalities.

Difficulty decrease: the sign of \(C_2\) is a one-step recurrence with a fixed negative value at order \(4\), and the length-six exclusion is one numerical comparison rather than an orbit search.

Preservation: the odd residue of \(u\), the congruence that makes the exit a single halving, and the exact integer parents are unchanged. The argument does not enlarge the class of maps or the length of a join.

## Not claimed

Finiteness of every residual excursion is not proved. A cover by joins of several excursions is not proved. Convergence of every orbit is not proved. No census is claimed, and the terminal-power classification is not claimed. The cutoff at length five is not uniform. The finite integer grid used as a check is not this theorem. The ratio of the exit to the seed is not proved to increase with \(u\); the identity above gives a nonnegative slack in the opposite arrangement.
