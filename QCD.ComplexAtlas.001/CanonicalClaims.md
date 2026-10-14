<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Canonical analytic and fractal claims: a bounded migration crosswalk

The source tree `/home/dell/collatz` is read-only. The canonical file is
`/home/dell/collatz/FINALEE.MD`, SHA-256
`5d62b3352f77a89bf0d29b296c31b1b13f7d3cac04b300cd8dcc8f5e6a5dd569`.
Destination line references below refer to the inspected baseline commit
`6fdf2f0c14c1f74ad8c06cfc527ff658edda6fab`, not to later shifted Markdown lines.

Two fresh read-only source reviewers inspected disjoint intervals under the
native asynchronous workflow `5cda53d3-b33b-4761-b37d-5cb492c407db`.
Their reports were read by the parent. Their source-proof inspection is **not**
a Lean run, a replay of source programs, or approval of the entire corpus.
The independently constructed [marked-cycle result](../QCD.ComplexCohomology.001/Resonance.md)
has separate mathematical statements and verification.

## 1. Coverage and conventions

**Exact target read:** `/home/dell/collatz/FINALEE.MD:3090-3278`, all 189 lines.

The crosswalk has **38 rows**: 34 numbered theorem/lemma entries, two finite-result entries, and two labelled reformulations. There is no separately labelled definition in this interval. Theorem 14.46 begins at the final requested line; its continuation was inspected as a dependency, not treated as additional interval coverage. Theorems 14.5–14.10 are not in this interval and are not covered here.

**Additional full source reading: 600 lines**, comprising:

| Source dependency | Lines read | Purpose |
|---|---:|---|
| `/home/dell/collatz/FINALEE.MD:31-76` | 46 | Raw, shortcut, accelerated and chronological-word conventions |
| `/home/dell/collatz/FINALEE.MD:3279-3298` | 20 | Completion of the boundary entry 14.46 |
| `/home/dell/collatz/research/papers/extracted-text/collatz-arithmetic-fractal-frameworks.pdf.txt:3500-3789` | 290 | Summable defect, integer avoidance, offset transport, eventual-periodic sign, entire interpolation and derivative freedom |
| `/home/dell/collatz/research/papers/extracted-text/collatz-arithmetic-fractal-frameworks.pdf.txt:3245-3356` | 112 | Parity isometry, affine cylinders, symbolic barrier, topology statement |
| `/home/dell/collatz/research/papers/extracted-text/collatz-arithmetic-fractal-frameworks.pdf.txt:2366-2434` | 69 | Eligibility, image capacity and its proof |
| `/home/dell/collatz/research/papers/extracted-text/collatz-arithmetic-fractal-frameworks.pdf.txt:2087-2131` | 45 | Clocked recovery proof and its inherited coordinate dependencies |
| `/home/dell/collatz/research/papers/extracted-text/collatz-arithmetic-fractal-frameworks.pdf.txt:2817-2834` | 18 | Reciprocal compactification and upper box-dimension definition |

Source searches were used for discovery. They are not counted as full proof reading or whole-family coverage. No external literature was retrieved.

### Mathematical objects that must remain distinct

- **Classical shortcut:** $`S(x)=x/2`$ on even states and $`(3x+1)/2`$ on odd states.
- **Raw classical map:** an odd affine step is $`3x+1`$, without the compulsory following division incorporated into the same tick.
- **Odd acceleration:** $`T(x)=(3x+1)/2^{v_2(3x+1)}`$.
- **Eligible integer set:** $`A\subseteq\mathbb Z_{>0}`$ such that $`S_c^L\vert_A`$ is injective for every $`L\ge0`$.
- **Symbolic barrier:**

```math

  \mathcal E=\{\varepsilon\in\{0,1\}^{\mathbb N_0}:3^{r_n(\varepsilon)}>2^n
  \text{ for every }n\ge1\}.

```

- **Its 2-adic image:** $`C_c=Q_c^{-1}(\mathcal E)`$.
- **Reciprocal compactification:** $`K_A=\{0\}\cup\{1/x:x\in A\}\subseteq[0,1]`$.

The source overloads $`E`$. The eligible integer set, symbolic barrier, and reciprocal compactification must not be silently identified.

### Reading tiers

- **S:** Exact source statement and supplied proof intuition read.
- **D:** Relevant additional definition or proof dependency read.
- **M:** Elementary derivation or counterexample checked in writing in this audit.
- **C:** Numerical/computational claim read, but its certificate was not independently replayed.
- **E:** Imported external theorem; external statement/proof still requires the parent's source check.
- Destination Lean evidence below means **actual statements and relevant proof source inspected**, not a fresh kernel build in this session.

## 2. Maintained destination evidence

These identifiers resolve the destination references in the crosswalk.

| ID | Precise maintained evidence | Actual semantics and limitation |
|---|---|---|
| **D1** | `Foundations.Main.StartHere/lean/DynamicalMorphisms.lean:57-83`, `AccumulatedClock`, `AccumulatedClockLower`, `VariableClockIterates` | Natural-valued accumulated clocks and exact iterated transport. Positivity implies clock growth. Does not state abstract composition, associativity or the proper finite-fiber periodicity equivalence. |
| **D2** | `QCD.TimeCompression.002/lean/CompressionOutcomes.lean:315-325`, `MagnitudeBoundedIffEventuallyPeriodic`, `CompressionEventuallyPeriodic` | Boundedness iff eventual periodicity on signed integer state space; periodicity equivalence for the specific common-power parameter compression. Not the abstract theorem 14.15. |
| **D3** | `QCD.ComplexAtlas.001/lean/ComplexPolynomials.lean:17-65`, `MinusNodes`, `PlusNodes`, `FiniteAgreementOnly`, `ModelDerivative`, `MinusMultipliers`, `PlusMultipliers` | Four complex polynomials, exact finite-node values, actual derivatives and differing multipliers. No entire function agreeing at every integer is constructed. |
| **D4** | `QCD.ComplexAtlas.001/lean/ComplexPolynomials.lean:76-154`, growth theorems and `OutsideEightPowers` | For these particular polynomials, radius $`8`$ implies full-sequence exponential exterior growth. Not symbolic or reciprocal fractal dimension. |
| **D5** | `Foundations.Main.StartHere/lean/AffineWords.lean:39-53,97-159,209-250,284-311` | Chronological rational affine composition; multiplier, denominator and full offset; fixed-point equation; legal raw-word closure implies the scalar equation. Does not prove that scalar closure supplies all intermediate guards. |
| **D6** | `Foundations.Main.StartHere/lean/Conductors.lean:18-55`, `ConductorCriterion`, `ConductorIntegralWitness` | For nonzero determinant, conductor divisibility iff the scalar integer equation has a solution. Not the all-phase denominator/guard profile. |
| **D7** | `QCD.Scaling.001/lean/GeneralizedScaling.lean:13-71`, `ScalingDivisibility`, `ScalingStep`, `ScalingIterates`, `ScalingReturnTimes` | Coprime scaling intertwines the raw integer map with offset scaled simultaneously, at the same raw clock. Not a constructed 2-adic itinerary map or rational-point divergence reduction. |
| **D8** | `QCD.CaptureChain.001/lean/CaptureChain.lean:16-29,57-77`, `LegalJoin`, `DecreasingCaptureChain`, `CaptureChainReachesOne` | An already supplied finite decreasing chain ending at $`1`$ yields raw capture. Does not assert universal coalescence-cell exhaustion or the source's finite-prefix descent induction. |
| **D9** | `QCD.ComplexCohomology.001/lean/ComplexCohomology.lean:20-25,42-86,237-266`; `QCD.ComplexCohomology.001/lean/ComplexLocalSystem.lean:88-146` | Field-guard collapse, ordered affine transport and scalar closure; genuine ordinary and twisted quotient spaces, including neutral quotient isomorphism to the coefficient field. These do not establish integral branch legality, the symbolic fractal, or the reciprocal compactification. |
| **D10** | `QCD.ComplexAtlas.001/ResearchAudit.md:159-173`; `QCD.ComplexAtlas.001/README.md:180-216,247-261` | Explicitly separates 2-adic cylinder displays from Julia geometry; records stronger integer-preserving entire interpolation as unmigrated. Numerical portraits are finite-time floating-point illustrations. |

The root `README.md` and `QCD.ComplexAtlas.001/README.md` were read completely; `QCD.ComplexAtlas.001/ResearchAudit.md` and `QCD.ComplexAtlas.001/lean/ComplexPolynomials.lean` were read completely. Relevant linked foundation, scaling, capture-chain, compression and cohomology statements were inspected.

Scoped searches of maintained Lean, TeX and Go sources did not locate the missing full statements identified below. “Missing” means **no matching destination statement found in this maintained-source inspection**, not an assertion about every archived source or ignored prototype.

## 3. Complete crosswalk

All source ranges in this table refer to **`/home/dell/collatz/FINALEE.MD`**.

| Exact source range and label | Preserved hypotheses / quantifiers | Checked mathematical status | Destination evidence | Tier | Exact unclosed bridge |
|---|---|---|---|---|---|
| **3090 — Adelic picture (reformulation)** | Positive-integer diagonal in $`\widehat{\mathbb Z}\times\mathbb R_{>0}`$; word length $`n`$, odd count $`r`$; inverse slope $`2^n/3^r`$. | Closed/discrete diagonal and displayed product balance are supported. Real height increments retain the additive correction. This is a reformulation, not arithmetic compactness. | Missing adelic destination. D5 retains affine data only. | S/M | Define the product-space dynamics and marked diagonal explicitly; preserve inverse versus forward multiplier convention. No escape/capture conclusion follows from this representation alone. |
| **3092-3095 — Theorem 14.1, compactness counterexample** | A sequence of changing positive seeds, compatible initial residues and increasingly long odd runs; not a single fixed seed. | **False as printed:** $`2(N+2)!-1`$ is not the sequence used in the proof. Corrected sequence $`2^{(N+2)!}-1`$ proves the intended obstruction. | Missing destination. | S/M | Migrate the corrected sequence with an explicit transcription-error disposition. Preserve the distinction between profinite convergence and a fixed integer trajectory. |
| **3096-3099 — Lemma 14.2, bounded diagonal stabilization** | $`x_N>0`$, $`x_{N+1}\equiv x_N\bmod2^N`$, one finite upper bound $`H`$. | Supported: eventually $`2^N>H`$, so successive differences vanish. A lower height bound is insufficient. | Missing destination. | S/M | Formalize the bounded-residue lemma; obtaining such an upper bound for relevant trajectories is a separate universal obligation. |
| **3100-3103 — Theorem 14.3, coalescence descent** | Every odd positive seed reaches $`1`$ iff every odd $`x>1`$ joins some smaller positive odd $`z`$; cells use positive-exponent words and exact terminal oddness. | Supported equivalence and affine cell algebra. **Cell exhaustion remains open**, as source states. | D5/D8 are partial infrastructure, not this equivalence or exhaustion. | S/D/M | Prove the exact cell-to-legal-word recovery and encode the strong-induction equivalence. Do not supply exhaustion by assumption. |
| **3104-3107 — Lemma 14.4, finite adelic box** | Finite prime set, one class per prime power, ordinary finite interval $`[u,v]`$. | Supported by CRT and spacing $`L=\prod p^{e_p}`$. Count at most $`1+\lfloor(v-u)/L\rfloor`$ if nonempty. | Missing destination. | S/M | Import/check CRT in the intended formulation; derive additional congruences from actual orbit identities rather than assuming them. |
| **3108 — Atlas / fractal synthesis (reformulation)** | Classical positive cycles; symbolic prefix barrier; stated finite counts and local cycle bounds. | **Barrier is misprinted:** $`3r_n>2^n`$ must be $`3^{r_n}>2^n`$. Conductor and dimension/numerical components have different proof dependencies; the summary is not one independent certificate. | D5/D6 cover scalar closure only; D10 distinguishes cylinders from Julia pictures. Other asserted components missing. | S/D/M/C | Repair the barrier; define the marked cyclic object and legal exponent class; check dimension and finite certificates separately. No full synthesis migration established. |
| **3110-3113 — Theorem 14.11, two-return descent** | $`n\ge1`$, odd $`u>0`$, $`x=2^nu-1>1`$, $`3^{n+1}u\equiv1\bmod2^{n+2}`$. | Descent and examples are supported. **Exponent description is wrong:** the last exponent is the single value $`t-1`$, not $`t-1`$ “ones.” | Missing destination. | S/M | Use exponent tuple $`(1^{n-1},2,t-1)`$; retain accelerated clock $`n+1`$, not raw ticks. |
| **3114-3115 — Finite result, exact guard densities** | All positive integers stratified by $`n=v_2(x+1)`$; specified one- and two-return congruences. | Exact densities $`1/3,1/12,1/16,17/48`$ follow by geometric series and intersection congruences. They are not complementary divergence densities. | Missing destination. | S/M | Supply the all-strata density proof, including the tail estimate; any excluded finite seed such as $`1`$ does not alter density. |
| **3116-3119 — Theorem 14.12, offset morphism/rational points** | Every positive odd $`c`$; $`z\in\mathbb Z_2`$; rational denominator condition for positive integer divergence. | Supported branchwise identities, itinerary scaling and $`C_c=cC_1`$. Rational-point divergence equivalence depends on 14.33. | D7 is raw integer scaling only; full statement missing. | S/D/M | Construct $`Q_c,C_c`$, prove scaling in $`\mathbb Z_2`$, then apply the checked integer-avoidance equivalence. |
| **3120-3123 — Theorem 14.13, eventual-periodic negative sign** | $`\varepsilon\in\mathcal E`$ eventually periodic; positive odd $`c`$ inherited from $`Q_c`$. | Supported: period drift is positive, tail fixed point is negative rational, inverse prefix branches preserve negativity. | Missing destination. | S/D/M | Formalize symbolic eventual periodicity and rational reconstruction. Does not assert that all rational inputs have periodic codes. |
| **3124-3127 — Theorem 14.14, clocked composition** | Arbitrary deterministic systems, natural-valued clocks; properness and finite fibers asserted separately. | Supported accumulated transport, composition formula, associativity and closure of proper/finite-fiber classes. | D1 migrates accumulated transport only. | S/D/M | Add the composite clock theorem, associativity and proper/finite-fiber closure. Single-state clock addition/multiplication is not a replacement. |
| **3128-3131 — Theorem 14.15, periodicity transfer** | A proper clocked morphism with finite fibers; each source state $`x`$. | Supported equivalence. Properness is needed forward; finite fibers are needed backward. | D2 proves a parameter-specific raw compression equivalence, not this abstract theorem. | S/M | State and prove the abstract finite-fiber theorem; include the finite transient target values in the reverse argument. |
| **3132-3143 — Theorem 14.16, entire interpolation and freedom** | Agreement at **every integer**, prescribed parity derivatives; positive shortcut cycles; arbitrary derivatives at any finite set of distinct integers. | **Displayed interpolant false.** Corrected entire interpolant, derivative formula, attracting-cycle multiplier and arbitrary finite derivative freedom are supported. | D3/D10 are explicitly **finite-node** countermodels; full integer-wide theorem missing. | S/D/M | Construct corrected $`F`$ and $`F+\sin(\pi z)g(z)`$. Prove integer-wide equality, derivative realization and shortcut cycle multiplier. Do not substitute raw-node polynomials. |
| **3144-3151 — Theorem 14.17, repetition clock** | Nonempty classical shortcut word; integer seed; $`j\ge0`$; separate zero/nonzero $`z_w(x)`$ cases. | Supported valuation clock and endpoint formula. The word-cylinder congruence, not mere arbitrary affine integrality, supplies itinerary legality. | D5 is affine infrastructure; complete repetition theorem missing. | S/M | Establish the shortcut word-cylinder lemma and apply it to $`w^j`$; handle $`z_w=0`$ without taking its valuation. |
| **3152-3155 — Theorem 14.18, nested terminal descent** | Finite nonempty pair family; $`\alpha_i>1`$, $`b_i,e_i\ge0`$, $`0<\beta_i<1`$, $`\alpha_i\beta_i<1`$; $`x\ge0`$. | Supported grammar induction, bound, strict descent and fixed-point bound. Classical $`O^3,E^2`$ threshold is $`19/5`$. | Missing destination. | S/M | Formalize chronological grammar semantics and invariant $`W(x)\le\max(x,X)`$; legal classical seeds form a separate guard obligation. |
| **3156-3163 — Theorem 14.19, threshold convexity** | Two affine contractions with nonnegative offsets; finite nonempty concatenations. | Supported exact convex-combination calculation. | D5 supplies composition only; threshold theorem missing. | S/M | Add positivity of the denominator and convex weights; no universal word-cover statement follows. |
| **3164-3171 — Theorem 14.20, finite rise fibers** | Positive odd seeds; $`F`$ a positive odd multiple of $`3`$; $`1\le j\le v_3(F)`$. | Fiber formula and common return endpoint are supported. The final $`G(2^{n+1}-1)`$ example needs its domain made explicit: on the stated domain, $`n`$ must be odd. | Missing destination. | S/M | Define complete return $`R`$, prove finite-fiber semiconjugacy and capture equivalence. State the domain of the final example. |
| **3172-3175 — Theorem 14.21, parity isometry** | Every positive odd offset $`c`$; all of $`\mathbb Z_2`$; binary metric $`2^{-k}`$ at first disagreement. | Supported **bijective isometry** and shift conjugacy. Nested compatible residue balls give existence and uniqueness. | No matching maintained theorem found. Valuation modules are not this theorem. | S/D/M | Construct the inverse limit/nested-ball inverse, prove exact distances and conjugacy. No positive-integer preservation follows from symbolic conjugacy alone. |
| **3176-3179 — Named external theorem 14.21a, truncated conjugacy** | Classical shortcut; solenoidal conjugacy fixing $`0`$; asserted order $`2^{n-4}`$, $`n\ge6`$; finite census through $`1000`$. | Classical order remains an imported result needing source verification. **Proof intuition falsely calls the two dynamics homeomorphisms.** Fixed-point census is only finite evidence. “Statements extend” cannot mean the same order for every odd $`a,b`$. | Missing destination/certificate. | S/E/C/M | Check the external classical theorem and family-specific hypotheses. Derive finite permutations from the conjugacy homeomorphism, not invertibility of the two dynamics. |
| **3180-3183 — Theorem 14.22, elementary capacity/table** | Fixed positive odd $`c`$; eligible **integer set**, all $`L\ge0`$; optimize $`0\le J\le L`$. | Capacity proof supported after restoring eligibility definition. Source's “set of … words” wording is not the actual integer-set hypothesis. Entries at $`L=10,20`$ checked below; larger entries unreplayed. | Missing destination. | S/D/M/C | Define $`M_c(J)`$, integer eligibility and binomial tails; migrate the proof and independently certify table/optimization. |
| **3184-3191 — Theorem 14.23, fiber packing** | $`n\ge1`$ actual accelerated sources in $`3`$-units; distinct successors; successor $`1`$ excluded. | Supported. Eligible fiber minima have density $`9/32`$; residue enumeration gives $`9v_j\ge32j-15`$, yielding the stated product bound. | Missing destination. | S/M | Formalize exact predecessor fibers, minimum classification and rank inequality; retain all three source restrictions. |
| **3192-3195 — Theorem 14.24, exact escape criterion** | An actual positive odd accelerated orbit; full-sequence escape. | Supported product identity and equivalence, using reciprocal summability of the corresponding escaping shortcut orbit. | Missing destination. | S/D/M | Connect the accelerated orbit to shortcut states and apply 14.38; unboundedness alone must not replace the stated full-sequence limit. |
| **3196-3199 — Theorem 14.25, Farey period bound** | Nontrivial positive cycle minimum $`\ge M`$; positive $`a,b,c,d`$, determinant one and strict logarithmic bounds. | Conditional theorem supported. Determinant and denominator sum checked; enormous power comparisons and verification prefix not replayed. | Missing destination/certificate. | S/M/C | Supply exact comparison certificates and independently checked prefix descent; preserve conditional versus verified-local conclusions. |
| **3200-3207 — Theorem 14.26, clocked recovery family** | Odd $`q\ge3,c>0`$; $`e\ge2,k\ge1`$; $`2^e-q>0`$, $`\beta<1`$; coordinate $`u`$, guard and legal seed relation inherited. | Recovery proof is supported with inherited coordinates. The exact interval leaves $`x,u,b`$ insufficiently defined. Example arithmetic is consistent. | Missing destination. | S/D/M | Read/check the preceding coordinate definition, including $`b`$, integrality congruence and seed positivity; then migrate guards, exact exponents, threshold and density. |
| **3208-3215 — Theorem 14.27, fixed-depth obstruction** | $`K\ge1`$, $`n>1`$, $`n\equiv1\bmod2^{2K}`$; canonical seed and return quotient $`P`$. | Closed formula and asymptotic obstruction are supported under the intended quotient semantics. The quotient/retraction definition was not fully read. | Missing destination. | S/M | Check the canonical retraction defining $`P`$, and that the displayed states stay canonical; then formalize the valuation induction. |
| **3216-3219 — Theorem 14.28, pending automaton boundary** | Finite states, one initial state, at most one pending edge per digit; least-significant-digit-first integer encoding. | Supported reachability equivalence and finite zero-tail exit bound. | Missing destination. | S/M | Make digit order and $`Z`$ explicit; a positive integer is a finite prefix containing $`1`$ followed by zeros. |
| **3220-3223 — Theorem 14.29, optimal counting exponent** | Eligible integer sets at fixed positive odd offset; $`\alpha^*\in(1/2,\log_3 2)`$. | Unique crossing, minimization and $`O(X^{\beta^*})`$ supported by capacity plus entropy tails. Displayed numerical enclosures not independently certified. | Missing destination. | S/D/M/C | Prove the uniform binomial-tail estimate and exact rational enclosure $`\beta^*<193077/200000`$; retain offset dependence in constants. |
| **3224-3231 — Theorem 14.30, reciprocal mass** | Offset $`1`$; integer eligibility intended, not symbolic $`\mathcal E`$. | Analytic/certificate architecture supported. The claimed exact rational computation through $`1025`$, tail and $`<23`$ certificate were not replayed. | Missing destination/certificate. | S/D/C | Resolve overloaded $`E`$, inspect the exact verifier and stored rational data, then check all capacity increments and tail inequalities. |
| **3232-3239 — Theorem 14.31, reciprocal box dimension** | Eligible integer $`A`$; $`K_A=\{0\}\cup\{1/x:x\in A\}`$; upper box dimension. | Supported covering proof and Hausdorff dimension zero. Rational comparison relies on 14.29's enclosure; $`193077/393077<1/2`$ checked exactly. | Missing destination. D4 is unrelated exterior polynomial growth. | S/D/M | Migrate count-to-cover lemma and dimension definition; certify the rational exponent enclosure separately. This is not symbolic or orbit-image dimension. |
| **3240-3243 — Theorem 14.32, escape-fractal topology** | Correct exponential barrier $`\mathcal E`$, positive odd $`c`$, $`C_c=Q_c^{-1}(\mathcal E)`$; admissible prefixes. | Supported nonempty compact perfect nowhere-dense topology, dense negative rationals, and $`-1,-5\in C_1`$. | Missing destination. D10 only discusses finite cylinder pictures. | S/D/M | Construct the symbolic closed set and parity isometry; prove extensions, forbidden continuations and dense rational reconstruction. |
| **3244-3247 — Theorem 14.33, integer-avoidance equivalence** | Each positive odd $`c`$; **existence** of a positive escaping seed iff $`C_c`$ has a positive integer point. | Supported, including the nontrivial forward bridge from 14.38. Does not prove $`C_1\cap\mathbb Z_{>0}=\varnothing`$. | Missing destination. Complex off-axis escape is a different theorem/domain. | S/D/M | Migrate summable defect, drift minimum and cycle-drift exclusion. Actual integer avoidance remains the genuine universal target. |
| **3248-3251 — Theorem 14.34, all-parameter raw profile** | Nonempty chronological legal-letter alphabet, signed $`q,c,d`$, admissible divisor; nonresonant $`\alpha\ne1`$; all phase denominators. | Supported for raw letter itineraries: integrality iff $`L\mid c`$, affine guards iff $`h_i\nmid t`$. However “first-division letters for $`H`$” must be reconciled with the example $`DA`$ and actual raw semantics. | D5/D6/D9 cover scalar closure/reconstruction only. Full phase-profile iff theorem missing. | S/D/M | State the exact alphabet/clock, read its conductor definitions, and prove all-phase integrality plus every guard. Scalar initial integrality alone is insufficient. |
| **3252-3255 — Theorem 14.35, finite-period certificate** | Positive integer period bound $`R`$; exact $`k_0(r)`$, $`M_r`$, $`B_R`$; descent certificates for every odd $`3\le m\le B_R`$. | Supported finite reduction by the cycle product identity and its minimum. No universal descent assertion is supplied. | Missing destination. | S/M | Implement/check exact finite thresholds and a sound descent certificate checker. Do not replace conditional finite coverage with numerical plausibility. |
| **3256-3259 — Lemma 14.36, descent induction** | Every integer $`2\le n<M`$ has an actual smaller positive shortcut iterate. | Supported by strong induction; nontrivial cycle minimum then $`\ge M`$. | D8 concerns supplied finite chains, not this universal bounded-prefix statement. | S/M | Add the bounded-prefix induction lemma and attach independently checked descent witnesses. |
| **3260-3261 — Finite result, descent census $`[2,2^{33})`$** | Exact half-open interval; two reportedly independent computations; specified counts, steps, longest descent and overflow controls. | Report read, **not independently executed or certified in this audit**. Cardinality decomposition is consistent. Not refuted because unreplayed. | No matching maintained census/certificate located. | S/C/M | Parent must inspect both implementations, input/data provenance and exact replay output. Preserve reported versus reproduced status. |
| **3262-3269 — Lemma 14.37, greedy majorization** | $`b_0=1`$, $`0\le b_{L+1}-b_L\le2^L`$; subsets of $`[1,2^K]`$ satisfying all dyadic cumulative bounds. | Supported finite prefix-count domination, summation by parts and harmonic integral bound. Verifier's checks through $`1025`$ not replayed. | Missing destination. | S/M/C | Formalize finite majorization; independently verify these hypotheses for the actual capacity sequence. |
| **3270-3277 — Lemma 14.38, summable affine defect** | Positive shortcut orbit, fixed positive odd $`c`$, infinite and nonperiodic. | Supported elementary proof. Injectivity, image count and two convergent geometric series give reciprocal summability and bounded $`R_n`$. | Missing destination. | S/D/M | Migrate the eligible-orbit counting lemma and bounded logarithmic defect; this is the key dependency for 14.24 and 14.33. |
| **3278 — Theorem 14.46, exact product-only threshold (opening fragment)** | Adjacent Farey neighbors of order $`R`$, enclosing $`\log_2 3`$; denominator and determinant conditions. Continuation inspected at 3279-3298. | Supported product-only threshold $`M_R=1+\lfloor1/(2^{c/d}-3)\rfloor`$. Larger decimal table and enclosures not replayed; prefixes are explicitly unverified. | Missing destination. | S/D/M/C | Certify Farey neighbors and real-expression enclosures. A product-compatible slope is not an actual cycle; unverified large prefixes remain unverified. |

## 4. Executed mathematical checks and corrections

### 4.1 Theorem 14.16: formula error, supported corrected theorem

The source displays

```math

F_{\rm printed}(z)=\frac z2+\frac14-
\left(\frac z2+\frac14\right)\cos(\pi z).

```


For every even integer $`n`$,

```math

F_{\rm printed}(n)=0,

```

and for odd $`n`$,

```math

F_{\rm printed}(n)=n+\frac12.

```

In particular, $`F_{\rm printed}(2)=0\ne1`$.

Its derivative at integers is

```math

F_{\rm printed}'(n)=\frac12-\frac12(-1)^n,

```

giving $`0`$ at even integers and $`1`$ at odd integers—not the stated slopes.

The corrected function is

```math

F_0(z)=z+\frac14-
\left(\frac z2+\frac14\right)\cos(\pi z).

```

It is entire, has the required shortcut values, and

```math

F_0'(z)=1-\frac12\cos(\pi z)
+\pi\left(\frac z2+\frac14\right)\sin(\pi z),

```

so $`F_0'(n)=1/2`$ or $`3/2`$ according to parity.

For distinct integer nodes $`n_i`$ and arbitrary prescribed complex derivatives $`d_i`$, choose the Lagrange polynomial $`g`$ satisfying

```math

g(n_i)=\frac{d_i-F_0'(n_i)}{\pi(-1)^{n_i}}.

```

Then

```math

G(z)=F_0(z)+\sin(\pi z)g(z)

```

has unchanged values at **every integer**, and $`G'(n_i)=d_i`$. Thus the stronger derivative-freedom result is supported, not merely conjectural.

For a positive shortcut cycle,

```math

y=\frac{3^r y+B}{2^L},\qquad B>0,

```

implies $`2^L>3^r`$. Its multiplier for $`F_0`$ is $`3^r/2^L<1`$. This proves attraction for this particular extension, not exhaustion of integer cycles.

**Destination distinction:** `QCD.ComplexAtlas.001/lean/ComplexPolynomials.lean:30-65` proves finite raw-node agreement and differing multipliers. For the minus models, derivatives at $`1,2`$ give

```math

(1/2)(-5/2)=-5/4,\qquad 0\cdot(-3/2)=0.

```

At $`3`$, the models return $`-3,0,-2,-10/3`$, respectively. These are neither the relevant raw values nor the shortcut value $`5`$. They do not constitute migration of integer-wide interpolation.

### 4.2 Theorem 14.1: factorial versus factorial exponent

The printed $`x_N=2(N+2)!-1`$ satisfies, for every fixed odd prime power and sufficiently large $`N`$,

```math

x_N\equiv-1\pmod{p^k},

```

not $`0`$.

Its proof instead uses

```math

\widetilde x_N=2^{(N+2)!}-1.

```

For this corrected sequence,

```math

S^j(\widetilde x_N)=3^j2^{(N+2)!-j}-1,

```

which is odd for the required initial range. Euler's theorem gives eventual residue $`0`$ at each odd prime power, while the 2-adic coordinate tends to $`-1`$. The profinite limit is not an integer diagonal point. Its real height escapes, so there is no compactness recovery of one fixed positive integer trajectory.

### 4.3 Exponential barrier and two-return clock

The literal synthesis guard $`3r_n>2^n`$ permits no prefix of length $`4`$, since $`r_4\le4`$ and $`12<16`$. It cannot describe the asserted nonempty perfect boundary. The correct guard is $`3^{r_n}>2^n`$.

For Theorem 14.11, after $`n`$ accelerated steps,

```math

y=\frac{3^nu-1}{2},\qquad
v_2(3y+1)=v_2(3^{n+1}u-1)-1=t-1.

```

Hence the next endpoint is

```math

z=\frac{3^{n+1}u-1}{2^t}
<\left(\frac34\right)^{n+1}(x+1)
\le\frac9{16}(x+1)<x

```

for odd $`x>1`$. The exponent tuple is $`(1^{n-1},2,t-1)`$. The supplied example $`11\to17\to13\to5`$ has exponents $`(1,2,3)`$.

The density sums are

```math

\sum_{n\ge1}2^{-2n}=\frac13,\qquad
\sum_{n\ge1}2^{-(2n+2)}=\frac1{12}.

```

Simultaneous guards require $`2^n\mid2`$, so their intersection occurs only at $`n=1`$, with density $`1/16`$. Their union has density $`17/48`$.

### 4.4 Parity isometry is supported; the dynamics are not homeomorphisms

The inverse branches

```math

f_0(z)=2z,\qquad f_1(z)=\frac{2z-c}{3}

```

partition $`\mathbb Z_2`$ into even and odd cylinders and scale distances by $`1/2`$. A length-$`n`$ code determines one residue ball modulo $`2^n`$. Compatible infinite codes determine a unique point. First disagreement at digit $`n`$ gives exact distance $`2^{-n}`$.

However, the 2-adic shift is two-to-one:

```math

S_{\rm shift}(0)=S_{\rm shift}(1)=0.

```

The classical shortcut is also two-to-one:

```math

T(0)=T(-1/3)=0.

```

The conjugacy is the homeomorphism; neither dynamic map is.

The family-wide order assertion requires qualification. At $`a=1,b=-1`$, the shortcut is the shift itself, and the normalized conjugacy is identity, with truncated order $`1`$. This contradicts extending the *same* $`2^{n-4}`$ order formula to every odd $`a,b`$. It does not refute the imported classical order theorem.

### 4.5 Capacity and fiber-packing constants

From the inspected capacity definition,

```math

M_c(J)=3^J+\left\lfloor\frac{c3^J}{2^J}\right\rfloor-c.

```

At offset $`1`$:

- $`L=10,J=5`$: $`M_1(5)=249`$, binomial tail $`386`$, total $`635`$, giving $`635/1024=0.6201171875`$.
- $`L=20,J=11`$: $`M_1(11)=177232`$, tail $`263950`$, total $`441182`$, consistent with the displayed ratio.

These computations check the displayed candidates, not exhaustive optimizer minimality at every table entry.

For 14.23, eligible minimum predecessors lie in four classes:

```math

\begin{aligned}
&x\equiv3\pmod4,\quad3\nmid x,\\ &x\equiv1\pmod8,\quad3\nmid x,\quad x\ne1,\\ &x\equiv13\pmod{48},\\ &x\equiv37\pmod{96}.
\end{aligned}

```

Their asymptotic density is

```math

\frac16+\frac1{12}+\frac1{48}+\frac1{96}=\frac9{32}.

```

Checking the ordered residues over one period $`96`$ gives
$`\max_j(32j-9v_j)=15`$; subsequent periods preserve that difference. The first minimum is $`7`$. Thus

```math

\begin{aligned}
\log P_n
&\le \log(22/21)+\sum_{j=2}^n\frac3{32j-15}\\ &\le \log(22/21)+\frac3{32}
 \log\left(\frac{32n-15}{17}\right),
\end{aligned}

```

which proves the stated bound.

### 4.6 Reciprocal topology and the divergence bridge

If $`N_A(X)\le CX^\beta`$, cover the reciprocal points with $`x\le X`$ individually and the tail by intervals covering $`[0,1/X]`$:

```math

N_\varepsilon(K_A)\le CX^\beta+1+\frac1{\varepsilon X}.

```

Taking $`X=\varepsilon^{-1/(1+\beta)}`$ gives upper box dimension at most $`\beta/(1+\beta)`$. Also, $`K_A`$ is countable, hence has Hausdorff dimension zero. Exactly,

```math

\frac{193077}{393077}<\frac12
\quad\text{because}\quad386154<393077.

```


This countable real compactification is not the perfect symbolic set $`\mathcal E`$ or its 2-adic image $`C_c`$.

For an infinite nonperiodic positive shortcut orbit, the inspected proof yields

```math

|A\cap[1,32^m]|
\le(c+1)27^m+(3125/108)^m.

```

The reciprocal-shell ratios are $`27/32<1`$ and $`3125/3456<1`$. Consequently,

```math

R_n=\sum_{\substack{j<n\\S_c^j(x)\text{ odd}}}
 \log\left(1+\frac c{3S_c^j(x)}\right)

```

converges. Escape therefore forces the multiplicative drift
$`D_n=r_n\log3-n\log2`$ to tend to infinity.

The drift attains a global minimum at a finite index. Distinct indices cannot have equal drift, by unique factorization. Shifting to that index gives a positive integer with every subsequent relative drift strictly positive—an element of $`C_c`$.

Conversely, an eventually periodic positive orbit would eventually accumulate the strictly negative drift of its positive cycle. This contradicts membership in $`C_c`$. Distinct positive integer states escape every finite set. This closes the equivalence in 14.33, **not** the arithmetic avoidance question.

For 14.32, closedness follows from forbidden cylinders. All ones supplies a point; sufficiently many added ones allow a later zero without breaking the guard, excluding isolated points. Sufficiently many zeros violate the guard, excluding interior. Appending all ones to any admissible prefix gives the dense negative rational points. The cycle

```math

-5\to-7\to-10\to-5

```

has repeating code $`110`$, whose prefixes satisfy the exponential barrier.

### 4.7 Farey and census sanity checks

The local Farey determinant is exactly

```math

111202\cdot125743-176251\cdot79335
=13\,982\,873\,086-13\,982\,873\,085=1,

```

and $`111202+79335=190537`$.

The census interval contains $`2^{33}-2=8\,589\,934\,590`$ integers, split equally into the stated odd and even counts. This validates cardinality consistency, not the reported trajectory replay, step count or overflow controls.

## 5. Findings, unresolved dependencies and next action

### Concrete source findings

1. **P1 — `/home/dell/collatz/FINALEE.MD:3132-3143`:** Entire interpolant has the wrong leading coefficient. Smallest correction: use $`z+1/4-(z/2+1/4)\cos(\pi z)`$; retain the supported integer-wide and derivative-freedom results.
2. **P1 — `/home/dell/collatz/FINALEE.MD:3092-3094`:** Factorial sequence contradicts the proof and odd-adic limit. Smallest correction: use $`2^{(N+2)!}-1`$.
3. **P1 — `/home/dell/collatz/FINALEE.MD:3108`:** Missing exponent makes the symbolic boundary empty. Smallest correction: $`3^{r_n}>2^n`$.
4. **P1 — `/home/dell/collatz/FINALEE.MD:3110-3112`:** Last accelerated exponent is incorrectly described as a run of ones. Smallest correction: the single exponent $`t-1`$.
5. **P1 — `/home/dell/collatz/FINALEE.MD:3176-3179`:** Noninvertible dynamics are called homeomorphisms; family order extension is underqualified. Smallest correction: attribute homeomorphism/permutation properties to the conjugacy and state checked family-specific order hypotheses.
6. **P2 — `/home/dell/collatz/FINALEE.MD:3168`:** Restrict the final $`G(2^{n+1}-1)`$ example to inputs in $`3\mathbb Z_{>0}`$, equivalently positive odd $`n`$.
7. **P2 — `/home/dell/collatz/FINALEE.MD:3180,3224-3236`:** Restore eligible-integer-set definitions and disambiguate the overloaded $`E`$.
8. **P2 — `/home/dell/collatz/FINALEE.MD:3200-3207,3248-3251`:** Make inherited seed coordinates and raw/first-division alphabet conventions explicit before migration.

These are source-audit dispositions. The source tree must remain unchanged under the assigned authority; corrections belong in parent-authored destination statements and provenance notes.

### Dependencies still requiring inspection or reproduction

- External classical truncated-conjugacy order theorem, including its normalization, “solenoidal” definition and generalized-family hypotheses.
- Full symbolic Hausdorff-dimension argument supporting the synthesis value $`H_2(\log_3 2)`$, and the exact 7,495-cylinder computation.
- Exact rational enclosures for $`\alpha^*,\beta^*`$.
- The reciprocal-mass verifier, capacity data through $`1025`$, and geometric remainder certificate.
- The two descent-census implementations and their exact independent outputs.
- Large integer inequalities in 14.25 and numerical enclosures/table in 14.46.
- Preceding seed-coordinate definition for 14.26 and canonical quotient/retraction definition for 14.27.
- Exact all-parameter letter convention for 14.34.

No external theorem is needed for the elementary corrected interpolation, parity-isometry construction, reciprocal covering lemma, topology construction, or summable-defect/divergence equivalence proved above.


## Migration checkpoint

This is a 38-row statement/proof-architecture crosswalk, not completion of the
source migration. The supported eligibility, parity-isometry, summable-defect
and integer-avoidance spine remains to be formalized with its actual definitions.
The reciprocal compactification, symbolic barrier and 2-adic image are distinct
spaces. Integer avoidance itself remains open. Numerical certificates remain
unreproduced until their verifiers and data are independently checked.
See the [cycle-lattice crosswalk](../QCD.ComplexCohomology.001/CycleSourceAudit.md)
for the separate seven-row source interval.
