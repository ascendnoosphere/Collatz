<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# No-crossing symmetric difference

Let \(h\) be a positive integer, and let the index window be the natural numbers strictly less than \(h\). For a finite set \(S\) of natural numbers, the shortcut numerator is
\[
A(S)=\sum_{j\in S}3^{\#\{k\in S:k>j\}}2^{j}.
\]
Let \(\mathrm{lo}<\mathrm{hi}<h\), and let \(C\) be a finite set of natural numbers contained in the index window, containing neither \(\mathrm{lo}\) nor \(\mathrm{hi}\), and containing no element strictly between them. The supports \(U=C\cup\{\mathrm{lo}\}\) and \(V=C\cup\{\mathrm{hi}\}\) are distinct, have equal cardinality \(r\), and satisfy
\[
U\triangle V=\{\mathrm{lo},\mathrm{hi}\}.
\]
In particular the symmetric difference has size \(2\). Writing \(s\) for the number of elements of \(C\) strictly above \(\mathrm{hi}\),
\[
A(V)=A(U)+3^{s}2^{\mathrm{lo}}\bigl(2^{\mathrm{hi}-\mathrm{lo}}-1\bigr).
\]
The equal-halves modulus \(M=2^{h}+3^{r}\) is coprime to \(6\). The third factor \(\theta=2^{\mathrm{hi}-\mathrm{lo}}-1\) satisfies \(0<\theta<2^{h}<M\). Thus if \(M\) divides \(3^{s}2^{\mathrm{lo}}\theta\), then \(M\) divides \(\theta\). That divisibility is impossible, so \(M\) divides neither \(\theta\) nor \(A(V)-A(U)\).

The factorization uses the empty open interval between the two moved indices. An element of the common support strictly between them, a symmetric difference of size other than \(2\), and divisibility by \(2^{h}-3^{r}\) are not treated. For \(h=6\), the supports \(\{4,5\}\) and \(\{0,2\}\) have symmetric difference of size \(4\), and \(2^{6}+3^{2}\) divides the difference of their numerators. Nothing here asserts that the classical Collatz map reaches \(1\).
