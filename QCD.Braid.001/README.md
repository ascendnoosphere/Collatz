# Saturated braid modulo \(D^2\)

Let \(D,n\in\mathbb{Z}\). The two-step state of \(n\) is \((D+1)\bigl((1-D)n\bigr)\). The product identity \((D+1)(1-D)=1-D^2\) makes \(D+1\) a unit modulo \(D^2\). If \(D\) does not divide \(n\), then \(D\) does not divide \((1-D)n\), and the two-step state is congruent to \(n\) modulo \(D^2\).

Let \(q=D+1\), let \(a\ge 1\), and let \(b\ge 0\). Suppose \(|D|\ge 2\), \(D\) does not divide \(c\), and \(q^{a+b}u\equiv c\pmod{D^2}\). The source states \(D^{a-k}q^{b+k}u-c\), for \(k<a\), are legal divided affine steps, the terminal value \(q^{a+b}u-c\) is divisible by \(D^2\), and two exact divisions equal that value divided by \(D^2\). The parent states \(D^{a+b-1-k}q^{k}u-c\), for \(k<a+b-1\), are legal divided affine steps. The gate \(q^{a+b-1}u-c\) is divisible by \(D\), the quotient is not divisible by \(D\), and one further divided affine step equals the same integer. The source seed therefore satisfies the two-step congruence.

Write \(Y(x)=(q-D)x+c\). If \(a\ge 1\), \(D\neq 0\), the word of \(a\) divided affine steps and two exact divisions at \(n\) is legal, the word of \(a-1\) divided affine steps, one exact division, and one divided affine step at \(p\) is legal, and the endpoints agree, then
\[
q^a\bigl((q-D)n-(D-1)c\bigr)-Dq^a(q-D)p=c(D-1)(q-D-1)D^a.
\]
If \(q\) and \(D\) are coprime as well, then \(q^a\) divides \(c(D-1)(q-D-1)\).

That divisibility does not produce a pair. For \(q=3\), \(D=2\), \(c=1\), and \(a=1\), the coefficient is \(0\), but \((n,p)=(1,1)\) fails the relation. For \(q=5\), \(c=1\), \(D=2\), and every \(a\ge 1\), no integers \(n,p\) satisfy the relation. The undivided second iterate need not return the seed modulo \(D^2\): at divisor \(2\) and seed \(1\), the value \(4\) divides once to \(2\), and \(2\not\equiv 1\pmod{4}\). Positivity of a parent is not claimed, and nothing here asserts that the classical Collatz map sends every positive integer to \(1\).
