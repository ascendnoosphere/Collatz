<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Canonical cycle-lattice claims: retained results and corrected failures

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

## Scope and coverage tiers

Both requested source intervals were read completely:

- `/home/dell/collatz/FINALEE.MD:1240-1266`;
- `/home/dell/collatz/FINALEE.MD:1808-1815`.

Necessary additional source reading was limited to **148 lines**, below the 400-line allowance:

- `/home/dell/collatz/FINALEE.MD:31-95`: map, alphabet, affine-offset and conductor definitions;
- `/home/dell/collatz/FINALEE.MD:103-140`: classical cycle criterion and rotation identity;
- `/home/dell/collatz/FINALEE.MD:504-518`: referenced conductor-parity argument and surrounding context;
- `/home/dell/collatz/FINALEE.MD:1674-1703`: generalized word conventions, marked rotation and recovery.

Here, **manual proof** means algebra derived in this report; **formal-source inspection** means the actual definitions, hypotheses and proof bodies were read—not that a proof checker was executed. **Documentation inspected** is not itself proof evidence.

No source code, build, test or external literature retrieval was executed. No files were modified.

## Seven-row claim crosswalk

Destination paths are relative to `/home/dell/Desktop/Collatz`.

| Exact source label/range | Hypotheses and claimed conclusion | Audited status | Maintained destination evidence | Coverage tier and residual obligations |
|---|---|---|---|---|
| **7.14**, `/home/dell/collatz/FINALEE.MD:1240-1242` | Nonempty classical accelerated word with positive exponents, $`k=\sum a_i`$, $`\Delta=2^k-3^r`$, $`B=\sum 3^{r-1-i}2^{s_i}`$. Positive odd cycle iff $`\Delta>0`$ and $`\Delta\mid B`$; cyclic cokernel, marked all-ones class, determinant; alleged exact-valuation failure. | **Cycle criterion, cokernel, marked class and determinant supported.** Smith-form proof intuition needs replacement. The displayed $`(1,1,2,4,3)`$ arithmetic is correct, but it is **not** a counterexample to exact accelerated recovery: it fails $`\Delta\mid B`$. Exact letter valuations follow when closure holds. | `Foundations.Main.StartHere/lean/AffineWords.lean:97-165` proves affine data and retained offset; `Foundations.Main.StartHere/lean/AffineWords.lean:306-311` proves scalar closure **assuming legal execution**. `Foundations.Main.StartHere/lean/GuardedRecovery.lean:37-58` recovers the raw clock from successful execution. These do not supply the full classical sufficiency or integer Smith theorem. | **Manual proof** below; **formal-source inspection** of supporting foundations. Migrate classical rotation/integrality/oddness recovery and the integer cokernel theorem. Do not describe word length $`r`$ as necessarily the primitive period. |
| **7.14a**, `/home/dell/collatz/FINALEE.MD:1244-1250` | $`\gcd(q,D)=1`$, $`D\nmid c`$, nonempty exponent word, $`\Delta\ne0`$. Claims exactness of $`0\to\mathbb Z\to\mathbb Z^r\xrightarrow{M_a}\mathbb Z^r\xrightarrow{\theta_a}\mathbb Z/\vert\Delta\vert\to0`$, all-ones kernel, cyclic cokernel and Smith form. | **Exact sequence false.** $`M_a`$ has zero kernel. **Cokernel and Smith form are nevertheless correct.** Rational diagonal factors are not integer units, and the closing edge remains twisted. | `QCD.ComplexCohomology.001/README.md:184-189`; `QCD.ComplexAtlas.001/ResearchAudit.md:92-105` diagnose the false kernel and integral-scaling argument. Actual field quotients appear at `QCD.ComplexCohomology.001/lean/ComplexLocalSystem.lean:88-145`, not an integer lattice quotient. | **Manual counterexample and corrected proof** below; **formal-source inspection** distinguishes coefficients. Replace the sequence by $`0\to\mathbb Z^r\xrightarrow{M_a}\mathbb Z^r\xrightarrow{\theta_a}\mathbb Z/\vert\Delta\vert\to0`$. Migrate its integer quotient isomorphism. |
| **7.14b**, `/home/dell/collatz/FINALEE.MD:1252-1256` | In the preceding cokernel, $`[c\mathbf1]=0`$ iff $`\Delta\mid cN`$; $`\operatorname{ord}[\mathbf1]=L=\vert\Delta\vert/\gcd(\vert\Delta\vert,N)`$. Claims cycle iff $`L=1,\Delta>0`$ for $`c>0`$, and identifies this with Definition 2.7. | **Class vanishing and order formula supported. Cycle criterion false for arbitrary $`c`$.** Correct algebraic condition is $`L\mid c`$. Also distinguish unscaled conductor $`L`$ from the conductor of the full offset $`cN`$. Positivity and guards require their actual parameter assumptions. | `Foundations.Main.StartHere/lean/Conductors.lean:18-59` proves the correct arbitrary-offset criterion. `Foundations.Main.StartHere/tex/Foundations.tex:200-219` gives its detailed proof and guard limitation. `Foundations.Main.StartHere/lean/RecoveryControls.lean:77-96` checks offset-sensitive reconstruction examples. | **Formal-source inspection** of the scalar criterion; **manual proof** of its torsion interpretation and counterexample below. Preserve the scalar theorem; add the marked quotient theorem and justified positive/exact-exponent recovery. |
| **7.14c**, `/home/dell/collatz/FINALEE.MD:1258-1260` | Classical shortcut on $`\mathbb Z_2`$. Claims $`\#\operatorname{Fix}(S^n)=2^n`$, $`\zeta_S(z)=(1-2z)^{-1}`$, and a continuum of periodic cycles, “almost all” non-integers. | **Fixed-point count and formal zeta function supported for $`n\ge1`$.** These count periods **dividing** $`n`$, not exact periods. The periodic set is countably infinite, not a continuum. “Almost all of these” has no specified measure or counting limit and is not established here. | `QCD.ComplexCohomology.001/README.md:189-194`; `QCD.ComplexAtlas.001/ResearchAudit.md:107-114` retain the countability correction. No maintained Lean theorem for this 2-adic fixed-point count was located. The different raw-map zeta example at `README.md:403-409` is not this theorem. | **Manual proof** below; **documentation inspected** for the existing correction. Migrate fixed counts, exact-period conversion and formal-series zeta semantics. No external parity-conjugacy theorem is needed for the proof supplied here. |
| **7.14d**, `/home/dell/collatz/FINALEE.MD:1262` | $`\lambda=D^K/q^r`$. Claims a three-factor adelic product, outcome blindness, classification by archimedean drift sign, and impossibility of finite-place separation. | **Rational product formula supported with correctly defined places and nonzero parameters.** Composite $`D,q`$ are not individual prime places. The total product is outcome-blind, but that does **not** make individual finite-place/residue information outcome-blind. The universal no-go assertion is false for the generalized raw family. | `QCD.SignedTraps.001/lean/SignedTraps.lean:286-341` identifies the actual finite residue walk and proves zero-avoidance iff no raw division. `QCD.ResidueLeakage.001/lean/ResidueCylinders.lean:986-997` proves full-sequence escape after division stops; `QCD.ResidueLeakage.001/lean/ResidueCylinders.lean:1128-1135` checks the ternary cycle return. | **Manual prime-factor calculation and exact dynamical counterexample** below; **formal-source inspection** of residue recovery. Retain only the product identity/outcome blindness of its **total value**; define aggregate notation explicitly and remove the universal no-go. |
| **7.14e**, `/home/dell/collatz/FINALEE.MD:1264-1266` | Binary prefixes, $`G_w=\mathbb Z/\vert2^n-3^{r(w)}\vert`$. Claims no canonical inverse system, modulus-divisibility witness, then impossibility of any prefix pro-homology/cohomological detector or finite-place route to a divergent seed. | **Specified generator-preserving reduction maps fail to exist along all edges.** The printed divisibility direction is reversed, and $`1\nmid5`$ is false. **Arbitrary inverse systems do exist**, for example with zero strict bonding maps. The sweeping consequences are unsupported. | `QCD.ComplexCohomology.001/README.md:187-189`; `QCD.ComplexAtlas.001/ResearchAudit.md:116-126` explicitly separate homomorphism existence from generator-preserving/surjective maps. `QCD.ComplexCohomology.001/tex/ComplexCohomology.tex:178` records the same limitation. | **Manual counterexample and corrected map contract** below; **documentation inspected**. State the required marks, direction and recovery property. Retain failure of that construction, not a theorem excluding all cohomology or deciding the divergent-seed statement. |
| **9.14-hybrid**, `/home/dell/collatz/FINALEE.MD:1809-1815` — requested interval begins at blank line 1808 | Nonempty phases, $`D\ge2`$, $`a_i\ge1`$, integer $`q_i,c_i`$, $`\gcd(q_i,D)=1`$. Claims cyclic integral cokernel via weighted $`\theta`$, unique rational solution, and integrality iff $`\theta(c)=0`$. | **Supported in full as an integer-lattice theorem.** Every $`q_i`$ really is coprime to $`\Delta`$. Nonzero $`\Delta`$ follows from the hypotheses for a nonempty word. No pairwise coprimality among multipliers is needed. This is not yet a positivity or branching-map theorem. | `QCD.ComplexCohomology.001/lean/ComplexCohomology.lean:29-82` proves phase-dependent field transport and unique nonneutral reconstruction. `QCD.ComplexCohomology.001/lean/ComplexLocalSystem.lean:126-145` defines the actual **field** quotient. `QCD.ComplexCohomology.001/README.md:138-147` preserves lattice guards and coefficient-reduction checks. **No maintained integer hybrid cokernel module was located.** | **Manual complete lattice proof** below; **formal-source inspection** of the field analogue. Migrate the integral quotient and reconstruction theorem, then separately prove any claimed positive/admissible branch interpretation. |

## Executed algebra and smallest repairs

### 1. Correct integer lattice theorem, including hybrid phases

Let $`r\ge1`$, $`D\ge2`$, $`a_i\ge1`$, and

```math

(Mx)_i=D^{a_i}x_{i+1}-q_i x_i,\qquad x_r=x_0,

```

with $`\gcd(q_i,D)=1`$. Put

```math

Q=\prod_iq_i,\quad K=\sum_i a_i,\quad
\Delta=D^K-Q,\quad
w_i=D^{s_i}\prod_{j>i}q_j.

```


Since $`Q`$ is coprime to $`D`$, $`D^K=Q`$ is impossible; hence $`\Delta\ne0`$. Also

```math

\gcd(D,\Delta)=1,\qquad \gcd(q_i,\Delta)=1.

```

Indeed, a prime dividing both $`q_i`$ and $`\Delta`$ would divide $`Q`$ and therefore $`D^K`$, contradicting $`\gcd(q_i,D)=1`$.

Weighted summation cancels all intermediate coordinates:

```math

\sum_iw_i(Mx)_i=\Delta x_0.

```

The two cyclic determinant terms give

```math

\det M=(-1)^{r-1}\Delta.

```

For $`r=1`$, the single entry is $`D^{a_0}-q_0`$, agreeing with this formula.

Here is direct **integral recovery**, without treating rational scaling as unimodular. Given integer $`c_i`$, solve the phase recurrence over $`\mathbb Q`$, starting at

```math

x_0=\frac{\sum_iw_ic_i}{\Delta}.

```

Composition gives endpoint closure. If $`\theta(c)=0`$, this $`x_0`$ is integral. For $`1\le i<r`$, prefix and suffix composition give integer offsets $`A_i,B_i`$ with

```math

D^{s_i}x_i=\Bigl(\prod_{j<i}q_j\Bigr)x_0+A_i\in\mathbb Z,

```


```math

\Bigl(\prod_{j\ge i}q_j\Bigr)x_i=D^{K-s_i}x_0-B_i\in\mathbb Z.

```

The two coefficients of $`x_i`$ are coprime. Bézout therefore implies $`x_i\in\mathbb Z`$.

Consequently $`\ker\theta=M\mathbb Z^r`$. The coefficient $`w_0=\prod_{j>0}q_j`$ is a unit modulo $`\vert\Delta\vert`$, so $`\theta`$ is onto. Thus

```math

\mathbb Z^r/M\mathbb Z^r\cong\mathbb Z/|\Delta|\mathbb Z.

```

The homogeneous recurrence and $`\Delta x_0=0`$ prove $`\ker M=0`$; rational solutions are unique.

This proves 9.14-hybrid and, by taking all $`q_i=q`$, the valid portion of 7.14a. The corrected sequence is

```math

0\longrightarrow\mathbb Z^r\xrightarrow{M}
\mathbb Z^r\xrightarrow{\theta}\mathbb Z/|\Delta|\mathbb Z
\longrightarrow0.

```


The cyclic cokernel yields Smith form
$`\operatorname{diag}(1,\ldots,1,\vert\Delta\vert)`$. Alternatively, for $`r\ge2`$, two $`(r-1)`$-minors are, up to sign,

```math

\prod_{i=0}^{r-2}q_i,\qquad D^{s_{r-1}},

```

which are coprime. The general Smith-normal-form theorem is the standard algebraic dependency for this final terminology; the quotient calculation itself was proved directly.

**Smallest kernel counterexample:** $`r=1,q=3,D=2,c=1,a=(1)`$. Then

```math

\Delta=-1,\qquad M=[-1],\qquad M\iota(1)=-1\ne0.

```

The asserted sequence is not even a complex at that composition.

**Integer-scaling failure:** For $`r=2,q=3,D=2,a=(1,1)`$, the claimed coordinate change includes $`x_1=(3/2)y_1`$, not an integer-lattice automorphism. Moreover $`x_r=x_0`$ becomes

```math

y_r=(D^K/q^r)y_0,

```

not ordinary periodicity unless $`\Delta=0`$. The actual matrix

```math

\begin{pmatrix}-3&2\\2&-3\end{pmatrix}

```

has one-dimensional minors $`2,-3`$, not a minor equal to $`1`$. Their gcd is $`1`$, which supplies the correct argument.

**Coprimality negative control:** If the hybrid coprimality condition is removed, $`D=2,a=(1,1),q=(2,4)`$ gives

```math

M=\begin{pmatrix}-2&2\\2&-4\end{pmatrix},\qquad \Delta=-4.

```

Its Smith factors are $`2,2`$, not $`1,4`$. For $`c=(1,0)`$, the displayed weighted obstruction vanishes modulo $`4`$, but the rational solution is $`(-1,-1/2)`$. The source’s actual coprimality hypotheses exclude this failure.

### 2. Classical recovery really supplies exact valuations

For classical positive exponents, every rotated numerator $`B_i`$ is odd and positive, and

```math

2^{a_i}B_{i+1}=3B_i+\Delta.

```

Because $`\Delta`$ is odd, $`\Delta\mid B_0`$ propagates to every $`B_i`$. With $`\Delta>0`$, define $`x_i=B_i/\Delta`$. These are positive odd integers and satisfy

```math

3x_i+1=2^{a_i}x_{i+1}.

```

Oddness of $`x_{i+1}`$ proves

```math

v_2(3x_i+1)=a_i.

```

This closes the recovery bridge; it is not merely rational fixed-point existence.

For the source’s witness,

```math

K=11,\quad \Delta=2048-243=1805,\quad
B=81+54+36+48+256=475.

```

At $`19`$, $`v_{19}(\Delta)=2>1=v_{19}(B)`$, so closure fails already. This is a useful **prime-power divisibility obstruction**, not failure of exact 2-adic letters after closure.

### 3. Conductor order, offset and positive branch recovery

Under the corrected quotient isomorphism, $`[\mathbf1]`$ maps to $`N`$, so

```math

\operatorname{ord}[\mathbf1]
=L=\frac{|\Delta|}{\gcd(|\Delta|,N)}.

```

Therefore

```math

[c\mathbf1]=0\iff L\mid c.

```

The full-offset conductor is instead

```math

\operatorname{ord}[c\mathbf1]
=\frac{L}{\gcd(L,|c|)}
=\frac{|\Delta|}{\gcd(|\Delta|,cN)}.

```

Thus $`L`$ must be named the **unscaled conductor** if Definition 2.7 uses the full affine offset.

**One-phase counterexample to $`L=1`$:**

```math

q=1,\quad D=2,\quad c=3,\quad a=(2).

```

Here $`\Delta=3,N=1,L=3`$, but $`x=1`$ is an exact positive accelerated fixed point:

```math

(1+3)/4=1.

```

If a multiplier $`q\ge2`$ is desired, $`q=3,D=2,c=5,a=(3)`$ gives $`\Delta=L=5`$ and the exact fixed point $`(3+5)/8=1`$.

For $`q>0,D\ge2,c>0`$, all rotated $`N_i`$ are positive. Consequently positive closure is equivalent to

```math

\Delta>0,\qquad L\mid c.

```

When additionally $`D\nmid c`$, an integral phase cannot satisfy $`D\mid x_i`$, because its row equation modulo $`D`$ would force $`D\mid c`$. Each output phase is therefore $`D`$-free, giving exactly $`a_i`$ whole-base divisions and legal subsequent affine branches.

These positivity assumptions cannot be silently extended to signed multipliers. For example,

```math

q=-3,\quad D=2,\quad c=5,\quad a=(1)

```

has the positive fixed point $`1`$, whereas the repeated presentation $`a=(1,1)`$ has $`\Delta=4-9=-5`$.

The hybrid theorem imposes no branch partition. For example, $`D=2,q_0=1,a_0=1,c_0=2`$ has the integral positive solution $`x_0=2`$, but the raw map divides $`2`$ rather than taking its prescribed affine branch. The hybrid **lattice theorem remains correct**; an admissible-orbit theorem needs additional guards.

### 4. 2-adic counts, exact periods and cardinality

The two inverse shortcut branches on $`\mathbb Z_2`$ are

```math

h_0(y)=2y,\qquad h_1(y)=(2y-1)/3.

```

They land in the even and odd classes respectively. Every length-$`n`$ binary word defines a composed inverse branch whose linear coefficient is $`2^n/3^r`$. Its fixed-point equation has a unique solution because $`3^r-2^n`$ is odd. Following the inverse branches verifies every parity guard. Distinct words have distinct length-$`n`$ itineraries, and every fixed point of $`S^n`$ supplies one such word. Hence

```math

F_n:=\#\operatorname{Fix}(S^n)=2^n,\qquad n\ge1.

```

As a formal power series,

```math

\exp\!\left(\sum_{n\ge1}\frac{F_nz^n}{n}\right)=\frac1{1-2z}.

```


The exact-period point count is

```math

E_n=\sum_{d\mid n}\mu(n/d)\,2^d,

```

and the exact-period orbit count is $`E_n/n`$. In particular, $`F_2=4`$ but $`E_2=2`$.

The union $`\bigcup_{n\ge1}\operatorname{Fix}(S^n)`$ is countable and infinite. Already $`n=1`$ has exactly the two ordinary-integer fixed points $`0,-1`$. The weakest correction is to retain the fixed counts and zeta function, replace “continuum” by “countably infinite,” and remove the unspecified “almost all” assertion.

### 5. Product formula does not erase finite-place obstructions

For nonzero rational $`\lambda`$,

```math

|\lambda|_\infty\prod_{p\text{ prime}}|\lambda|_p=1.

```

For $`\lambda=D^K/q^r`$, only primes dividing $`Dq`$ contribute. If $`D,q`$ are coprime, the source may define aggregate notation

```math

|\lambda|_D:=\prod_{p\mid D}|\lambda|_p,\qquad
|\lambda|_q:=\prod_{p\mid q}|\lambda|_p.

```

Composite numbers themselves are not prime places. For example $`D=4,q=9,K=r=1`$ uses the genuine places $`2,3`$:

```math

(1/4)\cdot9\cdot(4/9)=1.

```

If aggregate supports overlap, they must not be counted twice. For $`D=2,q=4,K=r=1`$, the doubly counted product would be $`2\cdot2\cdot(1/2)=2`$, not $`1`$.

**Exact counterexample to the universal finite-place no-go:** In the coprime raw family

```math

(q,c,D)=(2,1,3),

```

the seed $`1`$ has the positive cycle $`1\to3\to1`$. In contrast, residue $`2\bmod3`$ is invariant under the affine branch:

```math

2(2)+1\equiv2\pmod3.

```

Thus seed $`2`$ never divides and has

```math

F^j(2)=3\cdot2^j-1\longrightarrow\infty.

```

A finite residue certificate separates this divergent class from the displayed cycle. This does not solve classical Collatz; it refutes the generalized assertion actually stated.

Even at fixed classical multiplier data, $`a=(2,2)`$ and $`a=(1,3)`$ share $`\Delta=7`$ and the same drift, but their numerators are $`7`$ and $`5`$. The first closes at $`1`$; the second fails the obstruction at prime $`7`$. Drift sign alone does not certify an integral cycle.

### 6. Prefix maps: correct direction and bounded obstruction

For an extension $`w`$ of prefix $`w'`$, the proposed map

```math

\mathbb Z/m_w\mathbb Z\longrightarrow\mathbb Z/m_{w'}\mathbb Z,
\qquad [x]\longmapsto[x]

```

is well-defined exactly when

```math

m_{w'}\mid m_w.

```

For $`w'=11,w=110`$, the moduli are $`5,1`$. The map fails because $`5\nmid1`$, **not** because $`1\nmid5`$.

This is a valid small counterexample to generator-preserving natural reduction maps on all prefix edges. It does not exclude other bonding maps. Assigning zero maps to every strict extension and identity maps to equal nodes satisfies inverse-system composition, since compositions of strict zero maps remain zero.

The weakest correction is a no-go for the **specified marked reduction-map construction**. Any stronger theorem must specify the permissible systems and prove that they cannot retain enough information for the desired arithmetic recovery. No such universal bridge was established in the audited intervals.

## Maintained destination coverage ledger

| Destination inspection | Actual coverage |
|---|---|
| `Foundations.Main.StartHere/README.md` | Entire file read; links followed to conductor, affine words, guarded dynamics and recovery. |
| `QCD.ScalarConductor.001/README.md` | **Missing:** read returned `ENOENT`. Actual conductor implementation located at `Foundations.Main.StartHere/lean/Conductors.lean:18-59`. |
| `QCD.CycleObstruction.001/README.md` | **Missing:** read returned `ENOENT`. No replacement integer Smith/cycle-lattice module identified. |
| `QCD.ComplexCohomology.001/README.md` | Entire file read; field/integer distinctions and historical corrections checked. |
| `QCD.ComplexCohomology.001/lean/ComplexLocalSystem.lean` | Entire file read. Actual quotient is a field-linear quotient by cochains sharing one periodic potential; neutral and nonneutral alternatives checked semantically. |
| `QCD.ComplexCohomology.001/lean/ComplexCohomology.lean` | Entire file read. Ordered transport, closing equation, reconstruction, actual ordinary quotient and field guard collapse inspected. |
| `Foundations.Main.StartHere/lean/Conductors.lean`, `Foundations.Main.StartHere/lean/AffineWords.lean`, `Foundations.Main.StartHere/lean/GuardedDynamics.lean`, `Foundations.Main.StartHere/lean/GuardedRecovery.lean`, `Foundations.Main.StartHere/lean/RecoveryControls.lean` | Entire files read. Scalar offset theorem and legality premises preserved. |
| `README.md`, `QCD.ComplexAtlas.001/ResearchAudit.md` | Entire files read. Catalogue provenance was not treated as mathematical certification. |
| `Foundations.Main.StartHere/tex/Foundations.tex:181-244`; `QCD.ComplexCohomology.001/tex/ComplexCohomology.tex:151-187` | Relevant written proofs and status limitations read; TeX not compiled. |
| `QCD.SignedTraps.001/lean/SignedTraps.lean:108-144,280-342`; `QCD.ResidueLeakage.001/lean/ResidueCylinders.lean:962-1018,1100-1151` | Targeted proof-body inspection for finite-residue separation, escape and ternary cycle recovery. No broader density/analytic audit claimed. |
| Destination discovery searches | Lean/TeX/Markdown symbol searches and filename searches located the scalar conductor but no maintained integer Smith/hybrid lattice theorem or classical 2-adic fixed-count formalization. Searches respected tool ignore rules; they do not establish whole-corpus absence. |
| Configuration and working tree | Lean/Mathlib version `v4.32.2` inspected. Bounded `watchdog_diff` inspections showed no tracked delta; the two principal destination seams had no changes against reviewer-launch HEAD `6fdf2f0c14c1`. Unrelated untracked work was not audited. |

The field distinction is substantive: a nonneutral field quotient vanishes, while an integral matrix can retain nonzero torsion. For instance $`D=2,q=3,a=(3)`$ has integer matrix $`[5]`$ and cokernel $`\mathbb Z/5`$, but its rational twisted cohomology is zero. Field quotient results do not establish the integral Smith theorem.

## Unclosed bridges and next executable repair

1. **First repair:** migrate the corrected integral exact sequence and hybrid reconstruction proof above, using an actual quotient of $`\mathbb Z^r`$. State $`r\ge1`$, derive $`\Delta\ne0`$, and check the quotient map on concrete classes.
2. Specialize it to constant multipliers and prove the marked torsion-order theorem. Reuse the maintained scalar conductor criterion rather than duplicating or weakening it.
3. Prove positive/exact-exponent recovery with its stated parameter and guard assumptions; keep signed closure and phase-dependent algebra separate.
4. Migrate the supported classical 2-adic fixed counts and formal zeta statement, explicitly separating exact periods and cycles.
5. Replace universal no-go prose by the narrow product-value and marked-map obstructions actually established.

The manual arithmetic and recovery arguments above close the mathematical questions in this bounded lane. **Their missing destination implementations remain migration work.** This seven-row crosswalk is not completion of the comprehensive source corpus.
## Migration checkpoint

The supported integral cokernel and classical exact-recovery statements remain
formalization obligations; field cohomology is not a replacement for integral
torsion. The false initial kernel, offset-free conductor criterion, continuum
of periodic points, and universal cohomological no-go are not migrated as theorems.
The [analytic crosswalk](../QCD.ComplexAtlas.001/CanonicalClaims.md) covers a different source interval.
