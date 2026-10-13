<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# The dichotomy between a first hit and a trapped orbit

Let $`q,c,d,n\in\mathbb{Z}`$ with $`|d|\ge 2`$, and let the raw step be
```math
T(n)=\begin{cases} n/d, & d\mid n,\\ qn+c, & d\nmid n.\end{cases}
```
Write $`T^{0}(n)=n`$ and $`T^{j+1}(n)=T(T^{j}(n))`$. The offset sum is
$`U_{0}(q)=0`$ and $`U_{j+1}(q)=U_{j}(q)+q^{j}`$, equivalently
$`U_{j+1}(q)=q\,U_{j}(q)+1`$. The affine state is
```math
A_{j}(q,c,n)=q^{j}n+c\,U_{j}(q).
```
Time $`j`$ is a first hit of $`n`$ when $`d\mid A_{j}(q,c,n)`$ and
$`d\nmid A_{i}(q,c,n)`$ for every natural number $`i<j`$. The seed $`n`$ is
trapped when $`d\nmid T^{j}(n)`$ for every natural number $`j`$.

| # | Statement | Carried by |
| --- | --- | --- |
| .1 | **Raw prefix.** If $`d\nmid T^{i}(n)`$ for every $`i<j`$, then $`T^{j}(n)=A_{j}(q,c,n)`$. | `PrefixAffine` |
| .2 | **Affine guard.** If $`d\nmid A_{i}(q,c,n)`$ for every $`i<j`$, then $`d\nmid T^{i}(n)`$ for every $`i<j`$. The identification uses the raw-prefix formula at each earlier time. | `RawFreeOfAffineFree` |
| .3 | **Dichotomy.** Some time is a first hit of $`n`$ if and only if $`n`$ is not trapped. | `ExistsHitIffNotTrapped` |

The forward half starts from a first hit at time $`j`$. The affine states before $`j`$ are not divisible, so the raw states before $`j`$ are not divisible. The raw-prefix formula at time $`j`$ replaces $`T^{j}(n)`$ by $`A_{j}(n)`$, and divisibility passes to the raw iterate. Thus the orbit is not trapped.

The reverse half starts from the failure of trapping, so $`d`$ divides $`T^{j}(n)`$ for at least one $`j`$. Integer divisibility is decidable: $`|d|\ge 2`$, the remainder of division by $`d`$ is zero exactly on the multiples of $`d`$, and each raw iterate is a finite composition of such tests. The least-number operator on $`\mathbb{N}`$ is then applied to that decidable predicate and to the existence hypothesis. It returns the least time $`j_{*}`$ at which $`d`$ divides the raw iterate, and it rejects every earlier time. The raw-prefix formula identifies $`T^{j_{*}}(n)`$ with $`A_{j_{*}}(n)`$ and identifies each earlier raw state with the affine state, so $`j_{*}`$ is a first hit.

The least-number operator is the well-founded search that starts at time $`0`$ and accepts the first success. Its hypotheses are proved before it is used: decidability of $`j\mapsto(d\mid T^{j}(n))`$, and existence of one success, the latter by contradiction with the assumption that the seed is not trapped. No second minimum is constructed.

## Reduction record

**ORIGINAL OBLIGATION.** For every parameter record with $`|d|\ge 2`$ and every integer seed $`n`$, prove that there exists a first affine hit of $`n`$ if and only if it is false that $`d`$ divides no raw iterate of $`n`$.

**REPLACEMENT OBLIGATIONS.** (i) Define the affine state and the first-hit predicate. (ii) Prove that a raw prefix with no division before time $`j`$ equals the affine state at time $`j`$. (iii) Prove that an affine guard before time $`j`$ implies the raw guard before time $`j`$. (iv) Prove that divisibility of each raw iterate is decidable. (v) From failure of trapping, produce one divisible raw time and pass that existence statement, together with decidability, to the least-number operator. (vi) Prove that the returned least time is a first hit.

**RECOVERY ARGUMENT.** The time returned by the least-number operator is a time of the original raw orbit of the original seed. On the raw guard given by minimality, the prefix formula is an equality in $`\mathbb{Z}`$ between $`T^{i}(n)`$ and $`A_{i}(n)`$ for every $`i\le j_{*}`$. Divisibility by the original $`d`$ therefore transfers in both directions up to that time, which is the definition of a first hit. If instead the seed is trapped, the forward half has already shown that no first hit exists, so the existence hypothesis of the operator is not invoked. Both directions of the equivalence are recovered, and the witness is not replaced by a residue class or by a later clock.

**DIFFICULTY DECREASE.** The unresolved alternative was an infinite disjunction, that some raw time is divisible, against an infinite conjunction, that no raw time is divisible. The least-number operator replaces the disjunction by one index $`j_{*}`$, using well-founded descent on $`\mathbb{N}`$. The prefix formula is then an induction on that finite index, and every successor branch descends to the base time $`0`$. After those two descents, no divisibility search remains open. The argument does not retain a return exponent, a density estimate, or a core bound.

**PRESERVATION CONDITIONS.** The quantifiers remain every parameter record and every integer seed. The record still has arbitrary integers $`q`$ and $`c`$ and an integer $`d`$ with $`|d|\ge 2`$, so negative multipliers, offsets, divisors, and seeds remain. The first-hit clause still quantifies over every earlier time, not over a proper subset. Equality of states is equality in $`\mathbb{Z}`$. The trapped direction is kept: absence of every raw division is equivalent to absence of every first hit. No positivity, coprimality, or size restriction is added.

## What is not claimed

- The value of $`T^{m}(n)`$ at any time $`m`$ strictly after a time at which $`d`$ divides the state.
- A closed-form bound on the first time at which $`d`$ divides a state. The least-number operator supplies the least time without estimating it.
- A return map, a block length, or a residue-dependent exponent.
- Which trapped orbits are fixed points, translations, two-cycles, or escaping orbits.
- Any density of seeds, times, or residues.
- Convergence, divergence, or cycle structure of any classical Collatz orbit.
- That agreement on a finite parameter grid proves the equivalence for every integer outside that grid. The proof is the equivalence above.
