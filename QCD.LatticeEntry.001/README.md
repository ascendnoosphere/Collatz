<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Entry into the residue lattice before division

Let $q,c,D$ be integers and let $k$ be a natural number. Suppose
$$
D\nmid c,\qquad \gcd(c,D)=1,\qquad c\mid q^k.
$$
Write $A(n)=qn+c$. For every integer seed $n$, the state $A^k(n)$ is divisible by $c$. It is reached by $k$ applications of $n\mapsto qn+c$ and by no division. Every seed therefore meets the residue lattice $c\mathbb{Z}$ within $k$ affine steps.

This is not capture. Divisibility by $c$ does not assert that a raw iterate equals $1$. For $(q,c,D)=(2,2,3)$ and $k=1$, the hypotheses hold and the raw orbit of $2$ is the cycle $2\mapsto 6\mapsto 2$, which does not contain $1$.

The same hypotheses hold for every $k$ at $(q,c,D)=(3,1,2)$. The conclusion there is only that $1$ divides every integer. It is not the assertion that the classical raw map reaches $1$.
