<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Exact density and disjointness audit

**Status: AUXILIARY PROGRESS.** The arithmetic sub-obligation is closed.
Every displayed density fraction in `QCD.ClassicalCoalescence.001/README.md`
and `tex/ClassicalCoalescence.tex` was recomputed independently with exact
rational arithmetic; no value disagrees. The target itself remains open.

## Scope and method

Read both documents in full, then recomputed from the definitions, not from
the prose. Tools: Python 3 `fractions.Fraction` for exact rationals, integer
`v_2`, and direct residue enumeration. The main checks were:

1. Algebraic derivation of each density as a sum over `a = v_2(n+1)` and
   `b = v_2(3^a u+1)-1`, followed by exact geometric sums.
2. Exact enumeration of the parameter periods: `t mod 81` for every C and A
   row; `t mod 2592` for K; `t mod 648` for K_2075; `t mod 2^h 81` for the
   full A periods; `t mod 81` for K_27 and K_111.
3. Residue-class disjointness modulo 1024 (and 8192 for the two deep
   cylinders), plus the `mod 4` / `mod 256` terminal guards for S, H, J.
4. A direct membership scan for all odd `n <= 5,000,000` using only the
   defining predicates; densities matched to sampling error.
5. Reproduction of the finite-range counts quoted in the README for
   `n <= 1,000,000`.

I also checked every displayed cylinder identity, affine numerator, slope,
raw-clock count, and contraction inequality by simulation and by the affine
recurrence; these are not density claims but they feed the `a,u,b,v` tables.

## Claimed versus independently computed

| Quantity | Claimed | Independently computed | Check |
|---|---|---|---|
| CRT coefficient | `2/3-1/9-1/81` | `44/81` | exact |
| `d(R)` | `1/12` | `1/12` | exact |
| `d(R_*)` | `11/216` | `11/216` | exact |
| `d(R_* cap S_a)`, `a=2,3` | `11/1296` each | `11/1296` each | exact |
| `d(R_**)` | `11/324` | `11/324` | exact |
| `d(R_** cap 3Z)` | `1/48` | `1/48` | exact |
| `d(H)` | `7/131072` | `7/131072` | exact |
| `d(J)` | `7/16384` | `7/16384` | exact |
| `d(R_** cap H)` | `77/2654208` | `77/2654208` | exact |
| `d(R_** cap J)` | `77/331776` | `77/331776` | exact |
| `d(R_dagger)` | `89419/2654208` | `89419/2654208` | exact |
| `d(R_dagger cap 3Z)` | `8129/393216` | `8129/393216` | exact |
| `d(R_dagger cap C)` | `143/20736` | `143/20736` | exact |
| `d(R_dagger cap K)` | `341/165888` | `341/165888` | exact |
| `d(R_D)` | `65659/2654208` | `65659/2654208` | exact |
| `d(R_D cap A)` | `1529/442368` | `1529/442368` | exact |
| `d(R_D cap K_2075)` | `77/1327104` | `77/1327104` | exact |
| `d(R_D cap K_27)` | `11/11673330234144325632` | same | exact |
| `d(K_111)` | `1/71663616` | `1/71663616` | exact |
| `d(R_E)` | `6689147268412473047/315179916321896792064` | same | exact |

Decimals of the main chain: `1/12 = 0.0833333333`,
`11/216 = 0.0509259259`, `11/324 = 0.0339506173`,
`89419/2654208 = 0.0336895224`, `65659/2654208 = 0.0247376995`,
`d(R_E) = 0.0212232662`. The chain is strictly decreasing and `R_E` has
**positive density** (about `2.12%`), not density zero.

## Class counts, guards, and disjointness

| Count | Claimed | Independently computed |
|---|---|---|
| C classes modulo 1024 | 13 | 13 distinct: `175,199,287,367,431,455,507,583,687,711,815,943,967` |
| A classes modulo 1024 | 21 | 21 distinct: `47,71,155,191,231,303,347,423,543,603,623,679,763,799,839,859,879,927,935,1007,1019` |
| C rows: retained `t mod 81` | 44 per row | 44 for each of the 7 rows |
| K: retained `t mod 2592` | `44*31` | `1364` |
| K_2075: retained `t mod 648` | `44*7` | `308` |
| K_27: retained `t mod 81` | 44 | 44 |
| K_111: odd conditions | all | all 81 classes pass |
| A total retained | `417/65536` | `417/65536` |

The A period enumeration is decisive. Of the 21 rows, 15 retain all `44/81`
of the odd classes; three (`2203,231,1647`) retain `77/162 = (44/81)(7/8)`;
one (`2031`) retains `55/108 = (44/81)(15/16)`; and the two depth-ten rows
`347,423` retain `55/108` each. The resulting density is
`2(55/108)/2^10 + 15(44/81)/2^12 + 3(77/162)/2^12 + (55/108)/2^12`, which
sums exactly to `1529/442368`. Forbidden parameter classes found by solving
`3^b v = 129` or `43 (mod 256)` are `0,10 (mod 16)`; `1,0,4 (mod 8)`;
`1 (mod 16)`, matching the text.

Disjointness checks:

* C is disjoint from K: the C residues modulo 256 are `175,199,31,111,251,71,47`;
  `123` is absent. The 13 C classes modulo 1024 are distinct.
* A is disjoint from C and K: the 21 A residues modulo 1024 are distinct and
  avoid the 13 C classes and `123 (mod 256)`.
* K_2075 and K_27 share `27 (mod 1024)` but split modulo 8192: K_2075 is
  `2075 (mod 8192)`, K_27 is `27 (mod 8192)`; hence they are disjoint.
* K_111 is `111 (mod 1024)`, absent from C, A, K, and the two deep residues.
* S_2, S_3 are disjoint by exact `v_2(n+1)`.
* H and J are disjoint: the only shared initial rank is `a=4`, and the
  terminal guards `129` and `43 (mod 256)` differ.
* H, J do not meet S: their `a`-ranges are disjoint, except `J_2,J_3` versus
  `S_2,S_3`, where the terminal guards are `3 (mod 4)` versus `1 (mod 4)`.
* The full cylinders C, K, A, K_2075 do meet H or J on some parameter classes
  (e.g. A row `347` meets J at `t=0 (mod 16)`; K_2075 meets J at `t=5 (mod 8)`),
  but exactly those classes are removed by the `15/16`, `7/8`, `31/32`
  factors, so the **retained** parts used in the subtraction are disjoint.

Finite-range counts independently reproduced (exact, `n <= 1,000,000`):
`46,875` second-burst sources (`31,250` for `a=2`, `15,625` for `a=3`),
including `16,974` previously residual seeds; `484` paired-tail sources,
including `261` new residual removals and `163` multiples of three. These
match the README exactly. They are finite evidence, not a density proof.

## What the arithmetic proves

1. The CRT factor `2/3 - 1/9 - 1/81 = 44/81` is correct for every fixed
   dyadic class: `3` does not divide `u` is `2/3`; `n = 4 (mod 9)` and
   `n = 10 (mod 81)` are disjoint subsets of `n = 1 (mod 3)`.
2. The geometric sums over `a` and `b` give `d(R)=1/12`, `d(H)=7/131072`,
   `d(J)=7/16384`, and the `1/64` eligible second-burst densities.
3. The inclusion-exclusion for `R_*` is exact:
   `1/12 - 1/72 - 1/48 - 1/648 + 1/288 + 1/2592 = 11/216`.
4. The subtraction chain is legal: the 24 removed families are disjoint after
   intersection with `R_D`, so their densities add. The final rational
   `d(R_E)` is the exact difference, in lowest terms.
5. The reduction is not a density-zero elimination: `d(R_E) > 0`.

## What the arithmetic does not prove

* It does not prove **capture on `R_E`**. That remains the unproved bridge.
* It does not prove that every `n` outside `R_E` is captured; that needs the
  join identities, legality of every prefix, the parent inequalities, and the
  strong induction. Those are separate algebraic/logical claims (the written
  proofs and the Lean files address them; the density arithmetic does not).
* It does not prove that parent reduction terminates at `1` rather than at a
  member of `R_E`; it only shows termination at `1` or in `R_E`.
* It does not prove that `R_E` contains no cycle or divergent orbit. The
  positive density of `R_E` is compatible with either.
* It does not prove the Collatz conjecture, nor any positive-density capture
  statement. It is a reduction to a positive-density residual.

## Exact remaining non-arithmetic obligation

Prove that every `n in R_E` reaches `1`, or exhibit for every `n in R_E` a
positive smaller parent `p < n` with a legal join. Equivalently, close the
strong induction at `R_E`. The arithmetic has reduced the target to this
positive-density set (`d(R_E) = 0.0212232662...`); it has not produced a
descent or capture mechanism for the set itself. Merely replacing this
positive density by a smaller positive density would not prove capture.

## Reproducibility certificate

```python
from fractions import Fraction as F
crt = F(2,3) - F(1,9) - F(1,81)                  # 44/81
H = sum(F(1, 2**(a+11)) for a in (4,5,6))       # 7/131072
J = sum(F(1, 2**(a+10)) for a in (2,3,4))       # 7/16384
Rstar = F(1,12) - F(1,72) - F(1,48) - F(1,648) + F(1,288) + F(1,2592)
Rss = Rstar - 2*crt*F(1,64)                     # 11/324
Rd = Rss - crt*(H+J)                            # 89419/2654208
RD = Rd - crt*(F(13,1024) + F(31,8192))         # 65659/2654208
RE = RD - crt*(F(417,65536) + F(7,65536) + F(1, 2**59)) \
        - F(1, 2**15 * 3**7)                    # R_E
assert RE == F(6689147268412473047, 315179916321896792064)
```

The residue counts above were obtained by looping over the exact periods and
testing the defining predicates; the largest period used was `2^12 * 81 =
331,776` per depth-twelve A row.

## Bottom line

All displayed density and intersection fractions check exactly. Within this
audit's scope, the remaining obligation is capture on `R_E`, not another
subtraction of density fractions.
