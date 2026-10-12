SPDX-License-Identifier: CC-BY-4.0

# Cyclic two-run gap

Let a word be a finite sequence of exponents in \(\{1,2\}\). Its length is \(r\), its exponent sum is \(K\), and
\[
B=\sum_{i=0}^{r-1}3^{r-1-i}2^{s_i},\qquad
\Delta=2^K-3^r,
\]
where \(s_i\) is the sum of the exponents before position \(i\). Positive odd closure requires \(\Delta>0\) and \(\Delta\mid B\).

For the word \(1^p2^q\) with \(p,q\ge 1\),
\[
B=3^{p+q}+2^{p+2q}-2^{p+1}3^q
\]
and
\[
B-\Delta=2\cdot 3^q(3^p-2^p).
\]
If \(\Delta>0\) and \(\Delta\mid B\), then \(\Delta\mid(3^p-2^p)\) and
\[
0<\Delta\le 3^p-2^p,
\]
hence \(\Delta\cdot 3^q<3^{p+q}\). Whenever \(1\le q\le p\), one has \(2^{p+2q}<3^{p+q}\), so the determinant is negative. Thus no such positive divisibility exists for \(q=1\), nor for \(q=2\) and \(p\ge 2\). The remaining pair \(p=1\), \(q=2\) has numerator \(23\) and determinant \(5\), and \(5\) does not divide \(1=3-2\).

The word \(1^p\) has \(2^p<3^p\). The word \(2^q\) has numerator equal to the positive determinant \(4^q-3^q\), and \(4\cdot 1=3\cdot 1+1\). For \(K,r\ge 1\), \(|2^K-3^r|\) is coprime to \(6\). One rotation therefore preserves divisibility of the numerator by the determinant. Rotating \(1^p2^q1^s\) by \(p+q\) letters produces \(1^{p+s}2^q\), so the same gap applies, and the second block of length \(1\) or \(2\) is excluded.

## Reduction record

Original obligation: positive odd closure for a positive-exponent word on the letters \(1\) and \(2\) whose cyclic form has at most two blocks, other than a power of the letter \(2\).

Replacement obligations: the two-run identity; the bound \(\Delta\cdot 3^q<3^{p+q}\) under positive divisibility; exclusion of second-block lengths \(1\) and \(2\); the negative determinant of a power of the letter \(1\); the fixed point \(1\) of a power of the letter \(2\); and transfer of the same gap from \(1^p2^q1^s\) to \(1^{p+s}2^q\).

Recovery argument: the identities are equalities, and rotation preserves the determinant and the divisibility. This recovers the exclusion for second-block length at most \(2\), including the merged word \(1^p2^q1^s\). It does not recover an exclusion for every second block of length at least \(3\).

Difficulty decrease: an arbitrary two-block cyclic word is reduced to one ratio of block lengths and one divisibility. The cases of second-block length at most \(2\) are finite arithmetic. What remains for a longer second block is one exponential comparison, not an orbit search, and that comparison is not proved here.

Preservation conditions: the exponents stay positive, the cyclic form stays at most two blocks, and the pure power of the letter \(2\) stays as an exception. Removing that exception would deny the fixed point \(1\).

## What is not claimed

A second block of length at least \(3\) is not excluded. A word with four cyclic blocks, such as \(1^p2^q1^r2^s\) with all four exponents positive, is not excluded. It is not claimed that every positive integer reaches \(1\). The comparison \(2\rho\le\mu\le 4\rho\) is not this gap and is not proved. A finite integer grid checking the identities is not the theorem.
