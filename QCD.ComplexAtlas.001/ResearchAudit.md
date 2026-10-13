<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Complex QCD research: source coverage, model distinctions, and dispositions

This is a bounded, status-preserving audit of the complex/cohomological seam.
It is **not** a completed reconciliation of the entire source corpus. The
source repository `/home/dell/collatz` was kept unchanged. A manuscript title,
historical success message, extracted PDF, and its TeX source are not
independent proof certificates.

## Mathematical objects actually studied

| Object | Domain and retained structure | Executed gain | Unproved transfer |
|---|---|---|---|
| Raw lattice map | $`\mathbb Z[i]`$, $`\mathbb Z[\omega]`$, or a specified quadratic order; exact element divisibility, division precedence, raw clock | Coordinate division, all-seed off-axis $`(3,c,2)`$ escape for odd real $`c`$, and homogeneous Gaussian Bézout escape | No norm-only replacement of element/ideal dependence |
| Four-residue quotient | $`r=(x\bmod2)+(y\bmod2)\theta`$ and $`J_\pm(z)=(3z\pm r)/2`$ on nonzero residue; $`z/2`$ on zero residue | Integral numerator recovery and explicit nonreal cycles/fixed points | Not the raw fixed-offset map and not division by $`1+i`$ |
| Finite affine model | A declared finite quadratic quotient ring, map $`z\mapsto\theta z+1`$ | Exhaustive finite graph and cochain ranks | Raw division does not descend to this quotient |
| Ordinary cohomology | Finite marked orbit graph, incidence coboundary, explicit coefficient field | A real submodule quotient $`H^1`$ of a cycle is formally isomorphic to its coefficient field | Unmarked $`H^1`$ does not remember the cycle length or branch legality |
| Twisted transport | Ordered edges $`u_{j+1}=\lambda_j u_j+a_j`$, with nonzero multipliers for local systems | Closing equation $`(1-P)u_0=B`$ and potential reconstruction | Solving over a field does not produce an integral, admissible lattice orbit |
| Polynomial Julia model | One of four explicitly declared holomorphic polynomials | Exact finite node values, different cycle multipliers, and radius-$`8`$ escape proofs | No canonical extension of QCD, no Julia-to-integer implication |

For a field $`K`$ and $`d\ne0`$, $`d\mid z`$ holds for every $`z\in K`$ because
$`z=d(z/d)`$. Thus a literal raw field extension is just $`z\mapsto z/d`$.
Finite fields are useful here as **specified affine models and coefficient
fields**, not as an undisclosed substitute for a lattice division guard.

## Canonical destination evidence

- [Gaussian dynamics](../QCD.GaussianDynamics.001/README.md): full Lean source
  read and compiled. The explicit identity $`-q+(1+i)d=1`$ for $`q=2+i,d=2-i`$
  proves homogeneous escape despite equal norms. The residue homomorphism to
  $`\mathbb F_5`$ proves there is no common positive power.
- [Complex lattice descent](../QCD.ComplexLattice.001/README.md): full written
  proof and checked Lean. `ScalarTwoDivides`, `ScalarTwoQuotient`,
  `ScalarTwoUnique` and `CoordinatesIter` prove exact guards, unique quotient
  and all-time recovery in an actual free integral quadratic algebra. The
  dyadic transverse coefficient decreases to an odd coefficient within at
  most two raw ticks per factor of two; both exact tail coordinates are
  checked. The actual injective complex algebra embedding and its positive
  transverse norm bound recover `ComplexOffAxisEscape` for every real bound.
  The real axis is an explicit exception, not removed.
- [Complex cohomology](../QCD.ComplexCohomology.001/README.md): full written
  proof and checked Lean for the ordinary quotient, scalar transport,
  closing equation, general finite functional-graph dimensions and actual
  twisted quotients. The incidence kernel is identified with functions on
  genuine weak components; the neutral twisted quotient and homogeneous
  potentials have explicit linear isomorphisms to the coefficient field.
- [Quadratic fields and Galois groups](lean/ComplexFields.lean): actual field
  instances use the checked prime-modulus facts, the coefficient-field
  instances in Mathlib's `Algebra/Field/ZMod.lean`, and the checked no-root
  hypotheses of `Algebra/QuadraticAlgebra/Basic.lean`. A separate synthesis
  check confirmed actual `Field` instances rather than inferring them from
  a successful ring-theorem build. Frobenius equals conjugation, fixes
  precisely the coefficient field, and gives all two algebra automorphisms.
  Conjugation transports entire affine orbits with both parameters; nonzero
  square-zero elements certify that the ramified controls are not fields.
- [Polynomial countermodels](lean/ComplexPolynomials.lean): finite node
  equalities, actual complex derivative products and exterior growth checked
  in Lean. The Go pictures remain finite-time floating-point illustrations.
- [Quadratic arithmetic](../QCD.QuadraticArithmetic.001/README.md): existing
  coordinate and dyadic formal modules, exact Go arithmetic and written
  classifications. Compilation of those modules is not a claim that every
  written classification has been formalized.

## Source slices actually inspected

The independent source investigation opened the following specific slices.
Line ranges refer to the unchanged source tree, not the destination.

| Source | Reading coverage and disposition |
|---|---|
| `synthesis/L2/text/SYN-L2-013-transfer-protocols.tex:550-641` | Gaussian transfer proposal inspected; incompatible divisors and parity alphabets separated below |
| `synthesis/L2/text/SYN-L2-007-literature-generalized-collatz.tex:177-206` | Literature section inspected; general-divisor complex switch normalization is explicitly open |
| `archive/historical-notes/collatz_homological_no_go.md:1-171` | Entire historical note read; false exact sequence and overbroad no-go assertions rejected below |
| `archive/historical-notes/collatz_fractal_matrix_attack.md:1-145` | Entire historical note read; barrier counts and matrix limitations retained, one tail asymptotic corrected |
| `tools/verifiers/verify_homological_no_go.py:1-102` | Entire historical verifier read; not executed or trusted |
| `tools/verifiers/verify_escape_fractal.py:1-141` | Entire bounded/random verifier read; not executed or treated as a universal certificate |
| `src/collatz_research/qcd_continuous.py:1-170` | Real interpolation and affine candidate routines read; not a complex lattice implementation |
| `research/papers/extracted-text/collatz-arithmetic-fractal-frameworks.pdf.txt:3650-3789` | 2-adic image, offset transport, entire-extension derivative freedom and multiplier discussion inspected |
| `research/papers/extracted-text/collatz-astronomical-cycle-certificates.pdf.txt:137-241` | Accelerated cycle and finite-field obstruction formulas inspected; not a complete paper audit |
| `docs/ERRATA.md:350-379` | Canonical segregation of old verifier errors checked |
| `artifacts/organization/review-coverage.json:3782-3805` | Historical inventory/structural coverage checked; not semantic validation |

The investigation searched the source's documents, synthesis TeX, notes,
archive Markdown, extracted papers and Python code. A bounded exact-name
search did not locate Eisenstein-integer QCD dynamics. This is not an
exhaustiveness claim about every archive payload, HTML/JS visualization or
binary artifact. The Eisenstein calculations in this destination are
explicit new constructions with their own tests.

## Refuted historical routes and corrected obligations

### A nonzero determinant cannot support the alleged kernel

At `archive/historical-notes/collatz_homological_no_go.md:14-55`, a square
integer matrix $`M`$ with nonzero determinant is simultaneously claimed to
have an injected all-ones kernel. This is false: $`M`$ is invertible over
$`\mathbb Q`$, so its integral kernel is zero. Already the note's
$`q=3,D=2,a=(1,1)`$ example sends the all-ones vector to $`(-1,-1)`$.
Rational diagonal coordinate changes are not automatically unimodular
integral changes, and therefore do not prove the asserted Smith form.

**Disposition:** do not migrate the claimed exact sequence or its universal
no-go conclusion. A finite cokernel, an offset conductor, branch legality and
integral recovery would require separate corrected proofs. The new ordinary
and twisted cochain calculations do not rely on this route.

### Periodic 2-adic points are not an uncountable periodic set

At `archive/historical-notes/collatz_homological_no_go.md:79-83`, the alleged
continuum of periodic points conflicts with the stated binary-shift model.
For each period $`n`$, the shift has only $`2^n`$ fixed codes. The union over
positive integers $`n`$ is countable. Density and cardinality are different
properties; neither a 2-adic set nor interleaved binary display coordinates
make a complex Julia set.

### Homomorphism existence is not generator-preserving surjectivity

At `archive/historical-notes/collatz_homological_no_go.md:117-130`, zero
homomorphisms are overlooked and the printed statement that $`1`$ does not
divide $`5`$ is false. A homomorphism $`\mathbb Z/1\mathbb Z\to \mathbb Z/5\mathbb Z`$ exists, but cannot be surjective or preserve a
nonzero marked generator.

**Disposition:** an example can refute a particular marked bonding-map
construction; it does not exclude arbitrary inverse systems or all
cohomological approaches. The retained mark, direction of divisibility and
surjectivity requirement must be stated before a corrected obstruction.

The verifier at `tools/verifiers/verify_homological_no_go.py:39-55` shadows
the divisor with a determinant; lines 61–65 compare a conductor formula with
itself; lines 87–89 assert `5 % 1 != 0`. These are diagnosed errors, not new
verification results. `docs/ERRATA.md:370-377` already disowns the historical
finite checks; the additional prose failures above remain explicit.

### Gaussian alphabets and divisors cannot be silently exchanged

At `synthesis/L2/text/SYN-L2-013-transfer-protocols.tex:574-616`, an arbitrary
Gaussian divisor is announced, but formulas specialize to $`1+i`$ and then
invoke a four-class parity product map. The quotient by $`1+i`$ has two
classes; the quotient by $`2`$ has four. The corresponding guards, branch
formulas and cycle denominators are different.

**Disposition:** proposed sweeps, norm bounds and trichotomies are not
executed theorems. The destination explicitly separates raw $`d=2`$, raw
$`d=1+i`$, and the four-residue Joseph quotient. Units and equal norms do not
justify a parameter transport without offset, target and clock recovery.

### Finite branch closure is not raw branch legality

The accelerated arithmetic-fractal source uses formal affine returns over
finite fields. If a scalar closing denominator vanishes modulo a prime but
its numerator does not, the candidate is impossible over the integers.
That is a useful **necessary obstruction**. A compatible residue word or
solvable field equation still needs integral recovery and every original
branch guard. This is exactly the missing bridge retained by the new
transport/cohomology model.

### Fractal counts and interpolation are not a Julia transfer

The 7,495 depth-18 surviving cylinders in the extracted arithmetic-fractal
text are a bounded 2-adic display, not a complex Julia set or a Euclidean
dimension certificate. The historical binomial-tail claim that the tail is
its first term times $`1+o(1)`$ is also too strong: at a fixed threshold
$`\alpha>1/2`$, the ratio of the next term to the first tends to
$`(1-\alpha)/\alpha>0`$. This refutes that asymptotic without refuting its
weaker entropy-scale bound.

The source's entire-extension derivative-freedom calculation was read, but
is not imported as a formally verified general theorem here. The atlas
instead executes four exact finite-node polynomial countermodels: the same
selected cycle values have multipliers $`-5/4`$ versus $`0`$, or $`1475/54`$
versus $`0`$. Thus those finite values do not determine complex stability.
The stronger integer-preserving entire-extension statement remains an
explicit formalization item in the broader migration.

## Bounded literature checks

These sources were retrieved by the main agent, not by a delegated retrieval
loop. Metadata, definitions and statements are distinguished from full proofs.
No global originality claim is made from this bounded search.

- **[Kucinski00] Gina I. Kucinski, _Cycles for the 3x+1 Map on the Gaussian
  Integers_, May 2000 preprint.**
  [Original PDF](https://monks.scranton.edu/files/pubs/kucinski.pdf).
  Metadata, the four-residue map definition and principal statements were
  checked. The Joseph convention matches $`J_+`$ here. Its reported cycle
  enumeration is not imported as a complete cycle theorem or independently
  replayed certificate.
- **[Kionke17] Steffen Kionke, _A Geometric Approach to Divergent Points of
  Higher Dimensional Collatz Mappings_.** _Monatshefte für Mathematik_ 182
  (2017), 851–863; DOI `10.1007/s00605-016-0947-4`;
  [arXiv:1511.05893v1](https://arxiv.org/abs/1511.05893v1), submitted
  18 November 2015; [alphaXiv reader](https://www.alphaxiv.org/abs/1511.05893).
  Metadata and relevant lattice-map definitions were checked; no cone or
  density theorem is invoked to prove the new all-seed transverse descent.
- **[Chamberland96] Marc Chamberland, _A Continuous Extension of the 3x+1
  Problem to the Real Line_.** _Dynamics of Continuous, Discrete and
  Impulsive Systems_ 2 (1996), 495–509;
  [author-hosted PDF](https://chamberland.math.grinnell.edu/papers/3x_1996.pdf).
  Metadata was checked against the author's publication list. PDF text
  extraction was unreadable, so its proof was **not** claimed as read.
  The atlas's polynomial calculations are self-contained and not an
  implementation of that real-line extension.

The initial discovery also retrieved abstracts/full-text extracts for
arXiv identifiers `2609.33018`, `2607.23353`, and `2510.19456`. Those retrievals
are discovery coverage only, not imported theorem applications. No result
from them supplies the missing Julia-to-arithmetic bridge. Local BibTeX
entries for the three cited primary sources are in
[ComplexAtlas.bib](tex/ComplexAtlas.bib), using `amsalpha`.

## Checkpoint

**Closed obligations:** exact scalar-two guard, off-axis raw escape for odd
real offsets, explicit integral quotient cycles, ordinary cycle quotient,
finite functional-graph dimensions, actual twisted $`H^0,H^1`$ calculations,
ordered field closing equation, two explicit quadratic Galois groups and
same-clock affine conjugacy, finite-node multiplier countermodels and
mathematical exterior escape radii.

**Open obligations:** real-axis universal capture, other complex parameter
families, exhaustive infinite quotient basins/cycles, a useful marked
local-to-global arithmetic cohomology criterion, the stronger entire-extension
formalization, and any Julia-to-lattice transfer. Full corpus reconciliation
and the remaining migration tasks are still open; this audit does not replace
them with a narrower success claim.
