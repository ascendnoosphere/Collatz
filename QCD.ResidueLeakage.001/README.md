<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# QCD.ResidueLeakage.001 — exact raw cylinders and residue-leakage density

**Status:** checked positive-divisor theorem, exact finite evidence, and a refuted source
subclaim. Independent publication review is recorded separately in
[Verification.md](Verification.md). This is not a classification of the exceptional
infinitely-dividing seeds and not a proof of classical Collatz convergence.

The raw convention is division first:

```math
T(n)=\begin{cases}n/D,&D\mid n,\\qn+c,&D\nmid n.\end{cases}
```

The public escape theorem assumes $`q\ge2`$, $`c\ge1`$, $`D\ge2`$,
$`\gcd(q,D)=1`$, and positive initial seeds. Let $`F(r)=qr+c\bmod D`$ and let
$`m`$ be the **least positive** return time of $`0`$ under $`F`$.
A return exists because $`F`$ is a permutation, and $`1\le m\le D`$.
The accessible residues are $`A=\{F^j(0):0\le j<m\}`$.
The algebraic cylinder lemmas also allow $`c=0`$; the escape claim retains $`c\ge1`$.

**TL;DR.** At every depth $`h`$, seeds with at least $`h`$ actual raw division events
occupy exactly $`m^h`$ classes modulo $`D^h`$. If $`m<D`$, infinitely-dividing seeds
have ordinary natural density zero; the complementary density-one set has an
exact, division-free affine tail and escapes in the **full raw clock**.
If $`m=D`$, every seed divides infinitely often. A zero-density exceptional set can
contain cycles: $`(q,c,D)=(2,1,3)`$ has $`1\to3\to1`$ despite $`m=2<3`$.
The same example disproves the source's stronger claim $`m\mid D`$.

## Numbered results

| ID | Result and precise scope | Main formal anchors |
|---|---|---|
| QCD.ResidueLeakage.001.1 | Unit residue maps have a least positive zero return; the first raw division is recognized within delays $`0,\ldots,m-1`$, and failure means no later division. Natural states embed in the signed library's positive-divisor raw map at every clock. | `AccessExists`, `HitEventual`, `HitRawWitness`, `RawCast`, `IterateCast` |
| QCD.ResidueLeakage.001.2 | Exactly $`m^h`$ jointly legal source classes modulo $`D^h`$, with exactly $`m`$ children per legal parent. The cylinder test is equivalent to at least $`h`$ actual raw divisions, including immediate and consecutive divisions. | `RunShift`, `RunCoprime`, `ChildrenCard`, `ChildrenDisjoint`, `ClassesSucc`, `ClassesCard`, `SurvivesRawCount`, `SurvivesRawWindow` |
| QCD.ResidueLeakage.001.3 | Exact ceiling interval estimate, real-power survivor bound, and full-sequence **ordinary** density zero for infinite divisions when $`m<D`$; the complement has density one in both interval conventions. | `InfiniteDensityBound`, `PositiveInfiniteBelowMinBound`, `PositiveInfinitePowerBound`, `ResidueDensityZero`, `PositiveFiniteDensityOne` |
| QCD.ResidueLeakage.001.4 | Every finitely-dividing raw orbit has one division-free tail with its exact geometric-sum formula. With $`c\ge1`$ it escapes at every later raw clock; bounded and eventually periodic raw orbits are contained in the infinitely-dividing set. | `FiniteDivisionsTail`, `FiniteDivisionsFormula`, `ResidueEscape`, `BoundedInfinite`, `PeriodicInfinite` |
| QCD.ResidueLeakage.001.5 | The full-access boundary $`m=D`$ forces infinitely many raw divisions for **every** seed, without deciding boundedness or escape. | `FullAccessClasses`, `FullAccessInfinite`, `ClassicalPeriod` |
| QCD.ResidueLeakage.001.6 | A positive raw cycle inside the zero-density set, and a common-witness counterexample to the universal return-order assertion $`m\mid D`$. | `TernaryPeriod`, `TernaryCycleRun`, `TernaryCycleInfinite`, `PeriodNeedNotDivideModulus` |
| QCD.ResidueLeakage.001.7 | Reproducible finite census of legal classes, shared-parent source-digit lifts, and independent raw clocks for accepted **and rejected** sources. The infinite predicate is not computed. | `Census`, `Execute`, the eight Go tests, and [ResidueCylinders.json](other/ResidueCylinders.json) |

Lean: [ResidueCylinders.lean](lean/ResidueCylinders.lean) and
[ResidueDensity.lean](lean/ResidueDensity.lean).
Detailed proof: [ResidueLeakage.tex](tex/ResidueLeakage.tex).
Exact checker: [ResidueCylinders.go](go/ResidueCylinders.go) and
[ResidueCylinders_test.go](go/ResidueCylinders_test.go).

## Certified reduction and recovery

**Original obligation.** Prove that, for the fixed positive unit parameters with
$`m<D`$, positive seeds that eventually stop dividing and then grow affinely have
natural density one. The original target is about the deterministic raw map,
not a random walk and not just a compressed endpoint sequence.

**Replacement obligations.** A complete first-division search; preservation of all
previous guards when a source digit is appended; exactly $`m`$ legal children of
each common parent; disjointness and exhaustion of child classes; an interval
boundary estimate; and recovery of a single division-free raw tail.
All of these are proved in the linked Lean modules.

**Recovery argument.** A finite residue orbit proves that a division, if it ever
occurs, occurs within $`m`$ raw events. Composing complete searches recognizes
exactly the seeds with $`h`$ actual divisions. A legal depth-$`h`$ prefix has a
full raw witness time between $`h`$ and $`mh`$. Equivalently, survival is certified
by at least $`h`$ divisions in the first $`mh`$ raw events (`SurvivesRawWindow`).
Every infinite raw division witness
belongs to every finite-depth cylinder. Conversely, failure at some finite depth
recovers an actual raw time after which there are no divisions. The subsequent
states obey the original affine recursion, with no missing intermediate clocks.

**Difficulty decrease.** The obstruction was dependence of later guards on earlier
legal endpoints. A source shift by $`D^h u`$ retains the exact endpoint multiplier
$`P`$, so the next-digit map $`u\mapsto E+Pu\bmod D`$ is a bijection.
The legal fraction becomes exactly $`(m/D)^h`$ on complete residue blocks.
For fixed parameters, $`m/D<1`$ is a proved contraction in these counting bounds.
The finite boundary term tends to zero after the depth is fixed. The contraction
is not uniform over all parameter choices, and exhaustive enumeration costs $`D^h`$;
termination is not being presented as an efficient universal search.

**Preservation conditions.** Positive scalar divisor; division-first branch order;
$`q\ge2`$; $`\gcd(q,D)=1`$; the least **positive** return period;
$`c\ge1`$ for escape; and $`m<D`$ for density-one finite division.
No iid law, attainment assumption, genericity, compactness, or probabilistic source
is added. Signed negative-divisor dynamics are not silently replaced by $`D=\lvert d\rvert`$.

## The calculation

Let $`S_h`$ be the seeds with at least $`h`$ actual division events and $`I`$ the seeds
with infinitely many such events. For a successful prefix with endpoint $`E`$ and
numerator multiplier $`P`$, the exact shared-prefix identity is

```math
H^h(n+D^h u)=E+Pu,\qquad \gcd(P,D)=1.
```

Here $`H`$ is the partial first-division map, **not** the raw one-step map.
The formula is used only when the entire prefix is legal. In the code and Lean,
`Run` retains the endpoint and $`P`$, and failure is preserved by the same shift.
Thus every parent has exactly $`m`$ legal high digits, and

```math
\#(S_h\bmod D^h)=m^h.
```

For $`X>0`$, the exact ceiling bound and its explicit boundary form are

```math
\#(I\cap[0,X))\le\#(S_h\cap[0,X))
\le\min\{X,m^h\lceil X/D^h\rceil\},
```

```math
\frac{\#(I\cap[0,X))}{X}
\le (m/D)^h+\frac{m^h}{X}.
```

At $`X=0`$ all interval counts are zero; at depth $`h=0`$ the only class modulo one
is legal. If $`X\le D^h`$, the sharper count is at most $`m^h`$.
For any $`\varepsilon>0`$, first select $`h`$ with $`(m/D)^h<\varepsilon/2`$,
then select $`N>2m^h/\varepsilon`$. The bound is below $`\varepsilon`$ for **every**
integer $`X\ge N`$. This is a full-sequence ordinary natural-density limit.
It is not an interchange of an infinite intersection with natural density.
The source's closed positive interval $`[1,X]`$ is also treated exactly in Lean:

```math
\#(I\cap[1,X])\le\min\{X,m^h\lceil X/D^h\rceil\},\qquad
\#(I\cap[1,X])\le mX^{\log m/\log D}\quad(X\ge1).
```

The positive representative $`(n-1)\bmod D^h+1`$ retains the residue-zero right
endpoint and gives the exact ceiling, without replacing $`X`$ by $`X+1`$ in this bound.
A minimal integer scale $`X\le D^h`$ and the proved identity
$`(D^k)^{\log m/\log D}=m^k`$ recover the real-power display, including $`m=1`$.
For the density limit itself, inclusion in $`[0,X+1)`$ costs the factor
$`(X+1)/X\le2`$ for $`X\ge1`$; selecting tolerance $`\varepsilon/2`$ gives the
original positive normalization at every sufficiently large $`X`$.

For every $`n\notin I`$ there is one actual raw time $`t_0`$ such that

```math
D\nmid T^{t_0+j}(n),\qquad
T^{t_0+j}(n)=q^jT^{t_0}(n)+c\sum_{i=0}^{j-1}q^i
\quad(j\ge0).
```

The affine states increase by at least one per step when $`c\ge1`$.
This recovers escape for the same orbit and full raw clock.

## Boundary and counterexamples

- **Strict shortfall:** $`(q,c,D)=(2,1,3)`$ has $`A=\{0,1\}`$ and $`m=2`$.
  Infinitely-dividing seeds have density zero, but the raw cycle $`1\to3\to1`$
  is in that set. Its depth-$`h`$ endpoint is $`1`$ and its multiplier is $`2^h`$.
  An atomic source supported on this cycle gives the exceptional set mass one;
  the counting fraction is not a capture probability.
- **Refuted source subclaim:** this same admissible example has $`m=2\nmid3=D`$.
  The valid bound $`m\le D`$ suffices for the argument. The stronger assertion
  “order divides $`D`$” is false, not an unresolved proof obligation.
- **Full access:** classical $`(3,1,2)`$ has $`m=D=2`$. Every seed divides infinitely
  often, so finite-division density one is false for that map. This says nothing
  about the convergence or divergence of those infinitely-dividing orbits.
- **Nonunits are excluded:** $`(2,1,4)`$ need not return from the zero residue to zero.
  The exact checker rejects it instead of supplying an arbitrary search cap.
- **Zero offset is a finite-algebra control:** $`(2,0,3)`$ has $`m=1`$. The finite
  cylinder assertions still apply, but the public escape theorem keeps $`c\ge1`$.

## Source coverage and remaining obligations

Primary source: `/home/dell/collatz/FINALEE.MD:2019–2023`, Theorem 9.34,
SHA-256 `5d62b3352f77a89bf0d29b296c31b1b13f7d3cac04b300cd8dcc8f5e6a5dd569`.
The source remains read-only and is not copied into this family.
The density antecedent $`1\le m<D`$ already forces a positive divisor $`D\ge2`$;
no negative divisor is replaced by its absolute value in this argument.
The source's first-division convention and earlier residue arithmetic were checked;
[QCD.ResidueAccess.001](../QCD.ResidueAccess.001/README.md) supplies the existing
orbit, return-modulus, period, and cardinality lemmas.
The [source catalogue](../Library.SourceCatalogue.001/README.md) separately records
artifact identities and bytes; a byte identity is not a semantic proof.

**Closed positive-divisor obligation:** the density-one finite-division/affine-escape
half of Theorem 9.34, including exact joint cylinders, raw-event equivalence,
exact positive-interval ceiling survivor estimates, the real-power bound, and the
geometric-scale integer threshold.
**Refuted subclaim:** the introductory return-order divisibility assertion.
**Not declared complete here:** the source's conditional mean-slope, log-drift, and
pressure formulations; negative-divisor variants; the entire source artifact;
and the exhaustive corpus-to-result crosswalk. Those claims are not discarded or
downgraded because this bounded family has been completed.
The source's real-power quantitative display is proved in `PositiveInfinitePowerBound`,
with its original $`[1,X]`$ convention. The accompanying integer-scale estimate is
$`X\le D^h\Rightarrow\#(I\cap[1,X])\le m^h`$.
Real logarithms occur only in the proved analytic identity; no floating logarithm
is used in the exact finite checker.

## Reproduction and finite scope

Run from the repository root:

```sh
lake build ResidueCylinders ResidueDensity
CGO_ENABLED=0 go test -count=1 -v ./QCD.ResidueLeakage.001/go
CGO_ENABLED=0 go vet ./QCD.ResidueLeakage.001/go
make go GOFILE=QCD.ResidueLeakage.001/go/ResidueCylinders.go
make tex TEXFILE=QCD.ResidueLeakage.001/tex/ResidueLeakage.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
bash Scripts/CheckMarkdown.sh
bash Scripts/TestMarkdown.sh
bash Scripts/TestGitHubMath.sh
```

The executed census covers 132 unit parameter models with $`2\le q\le8`$,
$`2\le D\le9`$, $`0\le c\le3`$, and recorded depths $`0\le h\le4`$.
Every legal parent also checks all $`D`$ high digits at depth $`h+1`$.
It records **660 rows, 75,490 legal parent classes, 898,742 independent raw-clock
checks, and 589,658 source-digit lift checks**. The raw checks cover accepted
and rejected parents and children. Accepted sources recover their exact endpoint
and division count; rejected sources are independently checked through the
complete $`mh`$ or $`m(h+1)`$ raw-event window.

The implementation uses exact `math/big` arithmetic with reusable 4096-bit
capacity, explicit budgets, disjoint goroutine chunks, and stable record order.
Budget failure returns an error; no row is silently omitted.
Eight tests cover least periods, raw-clock edge cases, a 256-bit source shift,
strict/critical/zero-offset censuses, exact interval ceilings, rejected inputs and
budgets, zero allocations in the tested hot loops, and deterministic parallel assembly.
The finite report never decides the infinite predicate; the universal statements
come from the formal proofs and detailed recovery above.
