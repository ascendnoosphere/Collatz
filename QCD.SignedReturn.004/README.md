<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Magnitude of one affine return

Let $`q,c,n\in\mathbb{Z}`$ and let $`j`$ be a natural number. Write
$`U_{0}(q)=0`$ and $`U_{j+1}(q)=U_{j}(q)+q^{j}`$, and define the affine state
```math
A_{j}(q,c,n)=q^{j}n+c\,U_{j}(q).
```
A parameter record consists of integers $`q`$, $`c`$, and $`d`$ with
$`|d|\ge 2`$, hence $`d\neq 0`$. The time $`j`$ is a first hit of the seed
$`n`$ when $`d`$ divides $`A_{j}(q,c,n)`$ and $`d`$ divides $`A_{i}(q,c,n)`$
for no natural number $`i<j`$.

For every $`q,c,n\in\mathbb{Z}`$ and every natural number $`j`$,
```math
\bigl|q^{j}n+c\,U_{j}(q)\bigr|
\le |q|^{j}\,|n|+|c|\,\bigl|U_{j}(q)\bigr|.
```
The inequality is the triangle inequality. The absolute value of a product
and the absolute value of a power are equalities, so the direction remains
$`\le`$.

If $`d`$ divides an integer $`a`$, the exact quotient satisfies
$`d\cdot(a/d)=a`$, and therefore $`|d|\,|a/d|=|a|`$.

Consequently, if $`j`$ is a first hit of one seed $`n`$ for one parameter
record, then
```math
|d|\,\Bigl|\frac{A_{j}(q,c,n)}{d}\Bigr|
\le |q|^{j}\,|n|+|c|\,\bigl|U_{j}(q)\bigr|.
```
The left-hand side equals $`\bigl|A_{j}(q,c,n)\bigr|`$. The right-hand side is
the triangle majorant at the same seed and the same time. This is one seed
and one hitting time, not a uniform core.

| # | Statement | Carried by |
| --- | --- | --- |
| .1 | **Triangle.** $`\lvert q^{j}n+c\,U_{j}(q)\rvert\le \lvert q\rvert^{j}\lvert n\rvert+\lvert c\rvert\,\lvert U_{j}(q)\rvert`$. | `AffineTriangle` |
| .2 | **Exact division.** If $`d\mid a`$, then $`\lvert d\rvert\,\lvert a/d\rvert=\lvert a\rvert`$. | `NatAbsExactDiv` |
| .3 | **One return.** A first hit of one seed at one time obeys the same majorant after exact division by $`d`$. | `IsFirstHit`, `ReturnMagnitude` |

## Reduction record

**ORIGINAL OBLIGATION.** For every parameter record, every integer seed, and
every natural number $`j`$, if $`j`$ is a first hit of that seed, bound the
absolute value of the exact quotient $`A_{j}(q,c,n)/d`$ by data of that same
seed and that same time.

**REPLACEMENT OBLIGATIONS.** Prove the triangle inequality for
$`q^{j}n+c\,U_{j}(q)`$, using the absolute value of a product and of a power
only as equalities. Prove that exact division preserves absolute value.
Apply those two statements at the affine state named by one first hit.

**RECOVERY ARGUMENT.** Divisibility at the hitting time gives
$`d\cdot(A_{j}(q,c,n)/d)=A_{j}(q,c,n)`$, hence
$`|d|\,|A_{j}(q,c,n)/d|=|A_{j}(q,c,n)|`$. The triangle inequality at the same
$`q`$, $`c`$, $`n`$, and $`j`$ replaces that absolute value by the majorant
$`|q|^{j}|n|+|c|\,|U_{j}(q)|`$. The seed, the time, the multiplier, the
offset, and the divisor are the original ones. No orbit after the hit is
required for the comparison.

**DIFFICULTY DECREASE.** The quotient $`A_{j}(q,c,n)/d`$ is eliminated. The
remaining expression is a closed combination of $`|q|`$, $`j`$, $`|n|`$,
$`|c|`$, and $`|U_{j}(q)|`$. The decreasing resource is the number of
unevaluated absolute values of compound terms: the triangle step removes the
sum, and the product and power rules remove the remaining compound factors.
There is no residual search over earlier times inside the estimate.

**PRESERVATION CONDITIONS.** The triangle inequality quantifies over every
integer $`q`$, $`c`$, and $`n`$ and every natural number $`j`$, with no sign
or size restriction. The return statement quantifies over every parameter
record, hence every divisor with $`|d|\ge 2`$, every integer seed, and every
first-hit time. Absolute values retain negative multipliers, offsets,
divisors, and seeds. The inequality direction is $`\le`$. The statement is
not strengthened to a bound independent of the seed or the time.

## What is not claimed

- A uniform core, a bound independent of the seed, or a bound independent of
  the hitting time.
- Existence of a first hit for any seed, or any upper bound on the first time
  at which $`d`$ divides an affine state.
- The value of a raw iterate at any time after a hit.
- That the inequality is an equality. Cancellation may make it strict.
- Any density of seeds, times, or residues.
- Convergence, divergence, or cycle structure of any classical Collatz orbit.
- That agreement on a finite grid proves the comparison for every integer.
  On the grid used for the exact integer check, $`|q|^{j}<2^{20}`$. That
  restriction is an arithmetic convenience, not a hypothesis of the
  comparison.
