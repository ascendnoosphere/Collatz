SPDX-License-Identifier: CC-BY-4.0

# Three-affine closure

Let \(a,b,c,q\) be positive integers and let \(x,y,z\) be integers satisfying
\[
2^{a}y=qx+1,\qquad 2^{b}z=qy+1,\qquad 2^{c}x=qz+1.
\]
Set \(K=a+b+c\), \(\Delta=2^{K}-q^{3}\), \(B=q^{2}+q2^{a}+2^{a+b}\), and \(T=q^{2}+q2^{c}+2^{c+a}\). Then \(\Delta x=B\), so \(\Delta\) divides \(B\). The third state is recorded by \(\Delta z=T\) and \(z=T/\Delta\). The determinant is not zero, and both numerators are at least \(7\).

The same elimination, read on an arbitrary ordered triple of letters, is
\[
\bigl(2^{e_{1}+e_{2}+e_{3}}-q^{3}\bigr)u=q^{2}+q2^{e_{3}}+2^{e_{3}+e_{2}}
\]
whenever \(2^{e_{1}}u=qv+1\), \(2^{e_{2}}v=qw+1\), and \(2^{e_{3}}w=qu+1\).

## Reduction record

ORIGINAL OBLIGATION. An integer solution of the three affine equations exists only if \(\Delta\) divides \(B\), and the third odd state must be recovered from that solution.

REPLACEMENT OBLIGATIONS. Prove the ordered elimination identity above, specialize it to the word \((a,b,c)\) and to the rotated word \((c,a,b)\), and divide by the nonzero determinant.

RECOVERY ARGUMENT. The specialization \((e_{1},e_{2},e_{3},u,v,w)=(c,b,a,x,z,y)\) returns \(\Delta x=B\). The specialization \((b,a,c,z,y,x)\) returns \(\Delta z=T\). Since \(B\ge 7\), the relation \(B=\Delta x\) forbids \(\Delta=0\), and \(z=T/\Delta\) is the third component. Every hypothesis of the two specializations is one of the three given equations.

DIFFICULTY DECREASE. The obstruction was an unexpanded product of three affine letters. One subtraction identity removes that product. The remaining arithmetic is a finite expansion and a positivity bound of \(7\), with no further word search.

PRESERVATION CONDITIONS. The positive integers \(a,b,c,q\), the integer states, the value of \(\Delta\), and the two numerators are unchanged. No oddness, exact valuation, positivity of the states, or minimum state is added. Sufficiency is not claimed.

## What is not claimed

The divisibility criterion is necessary and is not sufficient for a legal cycle. The following are not proved:

- the classification of \(x^{2}+7=2^{n}\);
- the classification of \(x^{2}+D=2^{n}\) for odd positive \(D\);
- any bound on the number of solutions of \(x^{3}+D=2^{n}\);
- uniqueness of an odd multiplier \(q\);
- emptiness of three-affine closure for \(K>7\);
- a finite scan as a substitute for the identity;
- residue order, uniform contraction, and the classification of repunit divisors;
- escape from a profile, a discriminator, or phase rigidity;
- a parent chain, a family split, an excursion bound, or a cyclic gap;
- a terminal-power subfamily or a marginal repair;
- the comparison \(2\rho\le\mu\le 4\rho\).

A finite integer grid can only test the identity. It is not the theorem.
