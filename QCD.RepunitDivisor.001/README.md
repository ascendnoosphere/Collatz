<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Repunit divisibility

For integers $q\ge 1$ and $k\ge 0$, write
$$
G_k(q)=1+q+\cdots+q^{k-1},
$$
with the empty sum $G_0(q)=0$. The identity proved here is
$$
q^k=1+(q-1)G_k(q).
$$
Equivalently, $(q-1)G_k(q)=q^k-1$, so $G_k(q)$ divides $q^k-1$ and
$$
q^k\equiv 1\pmod{G_k(q)}.
$$
For $k\ge 1$,
$$
G_k(q)\equiv 1\pmod q
\qquad\text{and}\qquad
\gcd(q,G_k(q))=1.
$$
For every integer offset $c$ and every integer residue $r$, the $k$-fold map $x\mapsto qx+c$ therefore satisfies
$$
F^k(r)\equiv r\pmod{G_k(q)},
$$
where $F(x)=qx+c$. The closed value of the same iterate is $q^kr+c\,G_k(q)$.

The displayed cells are
$$
(q,c,D,k)\in\{(2,1,3,2),(2,1,7,3),(2,1,15,4),(3,1,4,2),(3,1,13,3)\}.
$$
On each cell, $D=G_k(q)$. Thus $D$ divides $q^k-1$, $D\equiv 1\pmod q$, $\gcd(q,D)=1$, and $k$ iterations of $x\mapsto qx+1$ return every residue modulo $D$.

## Reduction

ORIGINAL OBLIGATION. For each displayed cell, prove $D=G_k(q)$, the divisibility $D\mid q^k-1$, the congruence $D\equiv 1\pmod q$, the coprimality $\gcd(q,D)=1$, and the return $F^k(r)\equiv r\pmod D$.

REPLACEMENT OBLIGATIONS. Prove $q^k=1+(q-1)G_k(q)$ for every integer $q\ge 1$ and every $k\ge 0$, deduce the divisibility, congruence, coprimality, and affine return from that identity, and evaluate the five sums.

RECOVERY ARGUMENT. The evaluations $G_2(2)=3$, $G_3(2)=7$, $G_4(2)=15$, $G_2(3)=4$, and $G_3(3)=13$ identify each displayed divisor with the corresponding repunit sum. Substituting that equality specializes every general congruence to the displayed modulus. The offset on those cells is $c=1$, which is an admissible value of the arbitrary offset in the return congruence.

DIFFICULTY DECREASE. The induction parameter is the number of terms $k$. The successor step uses only the sum of length $k$ and the rule $qG_k(q)+1=G_{k+1}(q)$. The five displayed sums are finite arithmetic after that induction.

PRESERVATION CONDITIONS. The base remains an integer $q\ge 1$, the length remains a nonnegative integer, and the offset remains an arbitrary integer in the return congruence. No escape-density hypothesis, contraction hypothesis, cycle classification, or comparison of growth constants is added.

## What is not claimed

The argument does not claim that every positive orbit is eventually periodic or trapped, that escape has density one, or that a core is contracting. It does not claim that a raw cycle is unique. It does not claim the Hull–Dobell criterion, a conditional mean slope $1/k$, or the comparison $2\rho\le\mu\le 4\rho$. It does not claim a finiteness theorem for generalized Ramanujan–Nagell equations. A direct arithmetic check of the five cells does not replace the induction and does not extend the identity to an unproved parameter.
