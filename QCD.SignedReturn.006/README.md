<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# The first-hit clock

Let $q,c,d,n\in\mathbb{Z}$ with $|d|\ge 2$, and write $m=|d|$. The offset sum is $U_0(q)=0$ and $U_{j+1}(q)=U_j(q)+q^j$, equivalently $U_{j+1}(q)=q\,U_j(q)+1$. The affine state is
$$
A_j(q,c,n)=q^j n+c\,U_j(q).
$$
The time $j$ is a first hit of the seed $n$ when $d$ divides $A_j(q,c,n)$ and $d$ divides $A_i(q,c,n)$ for no natural number $i<j$. Let $r_0(n)$ be the class of $n$ in $\mathbb{Z}/m\mathbb{Z}$, and let $r_{i+1}(n)=q\,r_i(n)+c$.

| # | Statement | Carried by |
| --- | --- | --- |
| .1 | **One affine step.** For every $q,c,n\in\mathbb{Z}$ and every $j\in\mathbb{N}$, $A_{j+1}(q,c,n)=q\,A_j(q,c,n)+c$. | `AffineStateStep` |
| .2 | **Residue class.** The class of $A_j(n)$ in $\mathbb{Z}/m\mathbb{Z}$ equals $r_j(n)$, for every seed and every time. | `AffineStateCast` |
| .3 | **Divisibility.** For every $z\in\mathbb{Z}$, $d\mid z$ if and only if the class of $z$ in $\mathbb{Z}/m\mathbb{Z}$ is zero. | `DividesIffCastZero` |
| .4 | **First zero.** If $j$ is a first hit of $n$, then $r_j(n)=0$ and $r_i(n)\neq 0$ for every $i<j$. | `FirstHitResidue` |
| .5 | **Shift.** If $r_a(n)=r_b(n)$, then $r_{a+k}(n)=r_{b+k}(n)$ for every natural number $k$. | `ResidueAtAdd`, `ResidueAtAgree` |
| .6 | **Distinctness.** If $r_j(n)=0$ and every earlier class is nonzero, then $a<b<j$ implies $r_a(n)\neq r_b(n)$. A repeat would move the zero at time $j$ back to time $a+(j-b)<j$. | `ResidueAtDistinct` |
| .7 | **Clock.** If $j$ is a first hit of $n$, the classes $r_0(n),\ldots,r_{j-1}(n)$ are $j$ distinct nonzero elements of $\mathbb{Z}/m\mathbb{Z}$. Sending each to the predecessor of its canonical representative injects a $j$-element set into a set of cardinality $m-1$. Therefore $j\le m-1$. Since $m\ge 2$, one has $m>0$, so $j\le m-1$ yields $j<m$, and hence again $j\le m-1$. | `NonzeroIndex`, `FirstHitClock` |

The canonical representative of a class modulo $m$ lies in $\{0,1,\ldots,m-1\}$, and it is zero exactly for the zero class. A nonzero class therefore has representative in $\{1,\ldots,m-1\}$, and subtracting one lands in $\{0,1,\ldots,m-2\}$. Equality of those predecessors restores the representatives, hence the classes. Distinctness of the classes before time $j$ forces the times themselves to agree.

## Reduction record

**ORIGINAL OBLIGATION.** For every parameter record, every integer seed, and every natural number $j$, if $j$ is the first time $d$ divides the affine state of the seed, bound that time by the absolute value of $d$.

**REPLACEMENT OBLIGATIONS.** (i) Identify the class of each affine state with the iterate of $r\mapsto qr+c$ on $\mathbb{Z}/|d|\mathbb{Z}$. (ii) Convert divisibility by $d$ into vanishing of that class, in both directions. (iii) From a first hit, obtain a zero at time $j$ and nonzero classes at all earlier times. (iv) Prove that those earlier classes are pairwise distinct, by transporting a coincidence forward to an earlier zero. (v) Inject the $j$ earlier times into a set of cardinality $|d|-1$ and read both $j<|d|$ and $j\le |d|-1$.

**RECOVERY ARGUMENT.** The residue at time $i$ is the class of the original affine state $A_i(q,c,n)$, not of a different seed or a different multiplier. Vanishing of that class is equivalent to divisibility by the original divisor, because $d$ and $|d|$ divide the same integers. The first zero of the walk is therefore the original first hit, and the resulting inequality bounds that same time. The predecessor form and the strict form are the same natural-number bound once $|d|\ge 2$ has supplied $|d|>0$.

**DIFFICULTY DECREASE.** Before the argument, a first-hit time is an arbitrary natural number. After it, every admissible time lies in the fixed finite initial segment $\{0,1,\ldots,|d|-1\}$. The decreasing resource is the number of still-admissible times: the pigeonhole removes every candidate greater than or equal to $|d|$, and the injection that justifies the removal is a comparison of classes already known to be nonzero. The shift step that proves distinctness lowers the clock from $j$ to $a+(j-b)$, which is strictly smaller, so that branch decreases as well. No unbounded search remains.

**PRESERVATION CONDITIONS.** The coefficients $q$ and $c$ and the seed $n$ remain arbitrary integers. The divisor remains an arbitrary integer $d$ with $|d|\ge 2$, so negative divisors are included through $m=|d|$. The quantifiers are every parameter record, every seed, and every time. The hypothesis is a first hit, not the existence of one. Both $j<|d|$ and $j\le |d|-1$ are proved. No coprimality, positivity, or size restriction is added.

## What is not claimed

- A first hit need not exist. The residue walk may avoid the zero class at every time.
- The bound does not assert that $d$ divides $A_j(q,c,n)$ for any particular $j$, nor that $|A_j(q,c,n)|$ exceeds a prescribed value.
- Equality between a raw iterate and the affine state is not proved. The raw step after the hitting time is not described.
- No return map, block length, or residue-dependent exponent is constructed.
- No density of seeds, times, or residues is proved.
- Nothing is proved about convergence, divergence, or cycles of a classical Collatz orbit.
- Checking every modulus $m$ with $2\le m\le 15$, and every residue triple $q,c,n\in\{0,\ldots,m-1\}$, shows only that each first hit on that finite set occurs at a time strictly below $m$. It does not prove the bound for integers outside that set.
