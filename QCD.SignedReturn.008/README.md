<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# No uniform bound on one affine class

Let $`q,c\in\mathbb{Z}`$. Write $`T_0(q)=0`$ and
$`T_{j+1}(q)=T_j(q)+q^j`$, and define the affine state
```math
A_j(q,c,n)=q^j n+c\,T_j(q).
```
A parameter record consists of integers $`q`$, $`c`$, and $`d`$ with
$`|d|\ge 2`$. The time $`j`$ is a first hit of the seed $`n`$ when $`d`$
divides $`A_j(q,c,n)`$ and divides $`A_i(q,c,n)`$ for no natural number
$`i<j`$.

For every integer $`n_0`$ and every natural number $`j`$, if $`j`$ is a first
hit of $`n_0`$ and $`|q|^j\ge |d|`$, then there do not exist natural numbers
$`A`$ and $`B`$ with $`A<|d|`$ such that
```math
|d|\cdot\bigl|A_j(q,c,n)/d\bigr|\le A|n|+B
```
for every integer $`n`$ in the residue class of $`n_0`$ modulo $`|d|`$.

The proof uses the identity
```math
A_j(q,c,n+td)=A_j(q,c,n)+q^j td.
```
Divisibility by $`d`$ is therefore unchanged at every time, and the first hit
is unchanged. The sign $`\varepsilon\in\{1,-1\}`$ of $`d`$ satisfies
$`|d|=\varepsilon d`$, so the seed $`n_0+t|d|`$ is the integer shift of
$`n_0`$ by $`(\varepsilon t)d`$. For $`m\ge 1`$ and any prescribed natural
bound $`B`$, the explicit index $`t=|n_0|+B`$ satisfies
$`B\le |n_0+tm|`$. Choosing the bound
$`B+|c|\,|T_j(q)|+1`$ produces a seed $`n`$ in the original class, with the
original first hit, large enough that
```math
\bigl(|q|^j-A\bigr)|n|\le B+|c|\,|T_j(q)|
```
cannot hold. The coefficient is at least $`1`$ because
$`|q|^j\ge |d|>A`$. Exact division gives
$`|d|\cdot |A_j(n)/d|=|A_j(n)|`$, and the reverse triangle supplies the lower
estimate once the offset term does not exceed the linear term.

## Reduction record

**ORIGINAL OBLIGATION.** For a parameter record with $`|d|\ge 2`$, a seed
$`n_0`$, and a time $`j`$ which is a first hit of $`n_0`$ and satisfies
$`|q|^j\ge |d|`$, prove that no single pair of natural numbers $`A<|d|`$ and
$`B`$ bounds $`|d|\cdot |A_j(n)/d|`$ by $`A|n|+B`$ for every integer $`n`$ with
the same residue as $`n_0`$ modulo $`|d|`$.

**REPLACEMENT OBLIGATIONS.** Prove the affine shift identity and the
equivalence of divisibility at every time, hence the equivalence of first
hits after adding an integer multiple of $`d`$. Prove that $`t|d|`$ is such a
multiple by factoring out the sign of $`d`$. For the explicit index
$`t=|n_0|+B+|c|\,|T_j(q)|+1`$, prove
$`B+|c|\,|T_j(q)|+1\le \bigl|n_0+t|d|\bigr|`$. For that one seed, deduce
$`(|q|^j-A)|n|\le B+|c|\,|T_j(q)|`$ and contradict the size.

**RECOVERY ARGUMENT.** The seed $`n=n_0+t|d|`$ differs from $`n_0`$ by a
multiple of $`|d|`$, so it lies in the original residue class. The same
difference is $`(\varepsilon t)d`$, so the first-hit equivalence applies to
the original divisor, including a negative divisor. Exact division rewrites
the left side of the proposed inequality as $`|A_j(n)|`$. The false inequality
at this single original-class seed is the negation of the universal
quantifier over the class. No new restriction is imposed on $`q`$, $`c`$, or
$`d`$ beyond the standing admissibility $`|d|\ge 2`$, the first-hit
hypothesis, and $`|q|^j\ge |d|`$.

**DIFFICULTY DECREASE.** The original quantifier ranges over an entire
residue class. After the shift and the explicit choice of $`t`$, one integer
comparison remains. The decreasing resource is the number of seeds that still
have to be inspected: it falls from the class to one seed past a threshold
computed from $`B`$, $`c`$, and $`T_j(q)`$. The coefficient $`|q|^j-A`$ is a
positive integer, so that one comparison is impossible. There is no residual
child indexed by the class.

**PRESERVATION CONDITIONS.** The parameter record remains any integers
$`q,c,d`$ with $`|d|\ge 2`$. The seed $`n_0`$ and the time $`j`$ remain
arbitrary subject to the first-hit and power hypotheses. The class is the
original class modulo $`|d|`$, not a thinner subclass. Both signs of $`d`$ are
included. The pair $`A,B`$ is still one pair of natural numbers with
$`A<|d|`$, not a pair allowed to depend on $`n`$. The conclusion is still the
nonexistence of such a pair.

## What is not claimed

- The theorem does not say that every seed fails the inequality. A seed of
  small absolute value may satisfy $`A|n|+B`$ for a pair that fails on a
  larger seed of the same class.
- It does not say that no seed has a small quotient, and it does not forbid a
  bound whose coefficient $`A`$ is allowed to change with $`n`$.
- It does not assert that an arbitrary seed has a first hit.
- It assumes $`|q|^j\ge |d|`$ and $`A<|d|`$. Neither hypothesis is removed.
- It concerns the affine state at one fixed time, not a raw iterate after a
  division, and not a uniform bound over all times.
- The residue hypothesis is essential: the argument does not address integers
  outside the class of $`n_0`$.
