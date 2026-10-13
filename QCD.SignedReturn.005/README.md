<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Residue criterion for the first affine hit

Let $q,c,d,n\in\mathbb{Z}$ with $|d|\ge 2$, and write $m=|d|$. The offset sum is $U_{0}(q)=0$ and $U_{j+1}(q)=U_{j}(q)+q^{j}$, and it satisfies $U_{j+1}(q)=q\,U_{j}(q)+1$. The affine state is
$$
A_{j}(q,c,n)=q^{j}n+c\,U_{j}(q).
$$
Let $\pi:\mathbb{Z}\to\mathbb{Z}/m\mathbb{Z}$ be the canonical homomorphism, and let $\rho(r)=qr+c$ on $\mathbb{Z}/m\mathbb{Z}$. Time $j$ is a first hit of $n$ when $d\mid A_{j}(n)$ and $d\nmid A_{i}(n)$ for every $i<j$.

| # | Statement | Carried by |
| --- | --- | --- |
| .1 | At time zero, $A_{0}(q,c,n)=n$. The successor is $A_{j+1}(q,c,n)=q\,A_{j}(q,c,n)+c$. | `AffineState`, `AffineStateZero`, `AffineStateSucc` |
| .2 | For every integer $a$, the class $\pi(a)$ is zero if and only if $d$ divides $a$. | `CastZeroIffDvd` |
| .3 | **Cast.** For every seed $n$ and every time $j$, $\pi(A_{j}(n))=\rho^{j}(\pi(n))$. | `AffineCast` |
| .4 | The divisor meets $A_{j}(n)$ if and only if $\rho^{j}(\pi(n))=0$. | `AffineDvdIffResidueZero` |
| .5 | **First hit.** Time $j$ is a first hit of $n$ if and only if $\rho^{j}(\pi(n))=0$ and $\rho^{i}(\pi(n))\neq 0$ for every $i<j$. | `IsFirstHit`, `FirstHitIffResidue` |
| .6 | **Congruence.** If $\pi(n)=\pi(n')$, then $\rho^{i}(\pi(n))=\rho^{i}(\pi(n'))$ for every $i$, and $j$ is a first hit of $n$ if and only if it is a first hit of $n'$. | `ResidueIterateCongruent`, `FirstHitOfCongruent`, `FirstHitCongruent` |

The cast is proved by induction on $j$. The base state is the seed. At the successor, the offset recursion rewrites $A_{j+1}(n)$ as $q\,A_{j}(n)+c$, and $\pi$ sends that integer to one application of $\rho$. The zero class is the ideal $m\mathbb{Z}$, and $m\mathbb{Z}=d\mathbb{Z}$ because $m=|d|$. The first-hit equivalence is that dictionary applied at time $j$ and at every earlier time. Congruent seeds begin at the same class, so the inductive step of $\rho$ keeps their walks equal.

## Reduction record

**ORIGINAL OBLIGATION.** For every parameter record, every integer seed, and every time $j$, decide whether $j$ is the first time $d$ divides the affine state $q^{j}n+c\,U_{j}(q)$.

**REPLACEMENT OBLIGATIONS.** (i) Prove that the class of the affine state in $\mathbb{Z}/|d|\mathbb{Z}$ equals the $j$-th iterate of $r\mapsto qr+c$ starting at the class of the seed. (ii) Prove that this class is zero if and only if $d$ divides the affine state, and hence that a first hit is exactly a first zero of the residue walk. (iii) Prove that seeds with the same class have the same first-hit predicate at every time.

**RECOVERY ARGUMENT.** The canonical map $\pi$ is a ring homomorphism, so it sends $q\,A_{j}(n)+c$ to $\rho(\pi(A_{j}(n)))$. The successor identity $A_{j+1}(n)=q\,A_{j}(n)+c$ therefore transports the closed affine form onto the residue walk, with no change of seed and no change of clock. Zero in $\mathbb{Z}/m\mathbb{Z}$ is divisibility by $m$, and divisibility by $m=|d|$ is divisibility by $d$, in both directions. Applying that equivalence at the named time and at every earlier time recovers the first-hit predicate from the walk, and recovers the walk from the first-hit predicate. If $\pi(n)=\pi(n')$, every iterate agrees, so a first hit of either seed is a first hit of the other. A counterexample to either side of each equivalence is a counterexample to the other side, at the same time and for the same parameter record.

**DIFFICULTY DECREASE.** Divisibility of the integer $q^{j}n+c\,U_{j}(q)$, whose size grows with $j$, is replaced by iteration of one affine map on a fixed finite ring of cardinality $m=|d|$. The induction measure is the time $j$, and every successor lowers that time by one until the seed. Congruence then replaces an arbitrary integer seed by its class, a complete set of $m$ possibilities, without enlarging the walk.

**PRESERVATION CONDITIONS.** The parameter record is unchanged: $q$ and $c$ are arbitrary integers and $|d|\ge 2$, so negative multipliers, negative offsets, and negative divisors remain. The modulus is $|d|$, while divisibility is by $d$ itself; the two agree because $d=\varepsilon|d|$ for a unit $\varepsilon\in\{1,-1\}$. The quantifiers are every record, every seed, and every time. The first-hit guard forbids divisibility only at times $i<j$. No positivity, boundedness, or existence hypothesis is added.

## What is not claimed

- That some time $j$ is a first hit of a given seed. The residue walk may avoid zero at every time.
- That the affine state equals any raw iterate, including after a division-free prefix.
- The value of any raw iterate at a time after $d$ has divided a state.
- A bound on the least time at which $d$ divides an affine state, when such a time exists.
- A return map, a block length, or a residue-dependent exponent.
- Any density of seeds, times, or residues.
- Convergence, divergence, or cycle structure of any classical Collatz orbit.
- That agreement on the finite set $|q|\le 4$, $|c|\le 4$, $|n|\le 8$, $|d|$ from $2$ to $12$, and times $j\le 12$ proves the identities for every integer outside that set.
