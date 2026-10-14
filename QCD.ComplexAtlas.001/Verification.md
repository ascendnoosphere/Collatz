<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Executed verification and remaining obligations

## Scalar and profile update

The earlier sections below are **historical verification records**, with
counts belonging to their stated earlier batches. The update based on
`44d4687` has the following freshly executed checks:

- `make lean`: all **96 configured default targets**, 2,741 build jobs, passed;
  unchanged legacy linter warnings remain. `ScalarEscape` and
  `ProfilePrecision` are registered.
- A fresh Lean axiom audit of **29 added theorem declarations** passed;
  only `propext`, `Classical.choice` and `Quot.sound` occur. This covers the
  scalar guard/escape/order-transfer proofs, fixed precision, cyclic phase
  assembly and signed repunit formulas.
- `CGO_ENABLED=0 go test -count=1 ./...` passed all **66 locally present
  packages**; `CGO_ENABLED=0 go vet ./...` passed. Preserved untracked packages
  are not thereby published or semantically certified.
- Fresh `make tex` builds passed all 75 previously tracked documents plus
  `ScalarEscape.tex`, **76 documents**; both ignored-PDF/temp checks passed.
- `make go GOFILE=QCD.ComplexAtlas.001/go/ComplexAtlas.go` regenerated
  **25 vector PDFs and 25 PNG previews**, with all historical counts retained
  separately and six scalar rows adding 56,454 seeds. The combined lattice
  census has **178,771 seeds**. All six new PNGs were visually inspected;
  axes and titles were unclipped and the Eisenstein coefficient window is
  shown in its actual parallelogram embedding.
- The static Markdown regression suite passed **21 negative controls**;
  the GitHub payload fixture suite passed its 13 accepted and 18 rejected
  payload fixtures plus evidence/cache safety controls. Fixture success is
  not an actual API or live-browser rendering result.

The [repository audit](../Library.SourceCatalogue.001/RepositoryAudit.md)
records the six bounded semantic review lanes, corrected claims, a refuted
review finding, the uncompiled signed-return appendix and unread remainder.
The [297-item schema crosswalk](../QCD.ProfileDrop.001/SchemaAudit.md) separates
proved uses from candidates and missing definitions. No repository-wide
all-proofs-complete attestation or universal integer-axis theorem is made.

An isolated **staged-index checkout** passed Go tests and vet for its **60
published packages**, static checks for **85 maintained Markdown pages**, and
both script regression suites without borrowing any of the twelve untracked
research folders. This separates the published tree from the larger 66-package
working tree.

The actual authenticated GitHub GFM API checked **85 pages and 6,036 expressions**,
with exact source/HTML payload cardinality, order, display mode and TeX bytes.
The first run detected GitHub inserting a third backslash at a line-final cases
row separator. Keeping that separator and its next row on the same source line
removed the transport mutation; the strict checker was not weakened. This is
not live-browser layout inspection, MathJax execution or mathematical validation.
The evidence is stored privately under `.pi/Markdown/GitHub/`, not committed.

## Historical complex verification

This record covers the complex-ring, cohomology and visualization work, plus
repository-wide maintenance checks. It does **not** certify completion of the
source-corpus migration or resolve universal Collatz targets. The source tree
`/home/dell/collatz` was kept unchanged.

## Reproduction commands and observed results

Run from the repository root. The Makefile supplies the local Go path;
standalone Go and Lean commands may additionally need
`$HOME/.local/go/bin` and `$HOME/.elan/bin` on `PATH`.

| Executed command | Observed result and scope |
|---|---|
| `make lean` | Passed all 91 configured default targets, including every new complex module and the templates; some unchanged legacy modules emit linter warnings |
| `lake env lean .pi/Research/ComplexAxioms.lean` | Passed a generated audit of 190 owned declarations in nine modules and synthesis of both actual finite-field instances; only `propext`, `Classical.choice` and `Quot.sound` appeared |
| `CGO_ENABLED=0 go test -count=1 ./...` | Passed all 63 locally present Go packages, including the nine complex-atlas tests |
| Same Go command in an isolated checkout of the staged index | Passed all 57 packages actually included in this checked commit batch |
| `CGO_ENABLED=0 go vet ./...` | Passed |
| `gofmt -l` on all owned Go sources | No remaining formatting findings; eight preexisting tracked files received whitespace-only repairs |
| `make go GOFILE=QCD.ComplexAtlas.001/go/ComplexAtlas.go` | Passed the bounded atlas, finite-ring census and figure generation described below |
| `make go GOFILE=QCD.QuadraticArithmetic.001/go/QuadraticArithmetic.go` | Passed 372,704 exact arithmetic checks and regenerated seven quadratic figures |
| `make tex TEXFILE=...` for every maintained TeX document | A fresh full run compiled all 85 documents; the atlas document is rebuilt again after review corrections |
| `bash Scripts/CheckIgnoredPdfs.sh` and `bash Scripts/CheckIgnoredTexTemps.sh` | Passed after each TeX build; generated PDFs remain ignored and document-specific temporary files are cleaned |
| `bash Scripts/CheckMarkdown.sh` | Passed all 87 locally present mathematical pages; lexical math, local links, heading anchors and PNG assets |
| Markdown checker and regression tests in the staged-index checkout | Passed all 75 committed pages and the ten negative controls |
| Authenticated GitHub GFM API rendering of all 75 committed Markdown pages | GitHub recognized 4,907 math expressions |
| Chromium with MathJax 3.2.2, compiling those decoded expressions to SVG | All 4,907 compiled with zero math errors |
| `bash Scripts/TestMarkdown.sh` | Passed an accepted fixture and ten negative controls for the Markdown checker |
| `git diff --check` | Passed before the final review barrier |

The generated axiom-audit file and raw logs are local diagnostic artifacts,
not tracked proof sources. Its reproducible operation is to import
`GaussianDynamics`, `QuadraticArithmetic`, `DyadicArithmetic`,
`ComplexCohomology`, `ComplexGraph`, `ComplexLocalSystem`, `ComplexLattice`,
`ComplexPolynomials` and `ComplexFields`; synthesize `Field` for
`GeneralizedCollatz.ComplexFields.GaussianNine` and `EisensteinFour`; and run
`#print axioms` on their owned declarations. The checked mathematical sources
are linked below. This audit does not replace semantic review.

## Exact mathematical scope

| Module | Checked obligations | Not asserted |
|---|---|---|
| [GaussianDynamics](../QCD.GaussianDynamics.001/lean/GaussianDynamics.lean) | Exact Gaussian divisibility, finite division-prefix budget, Bézout avoidance, homogeneous full-sequence escape, and the equal-norm split-prime counterexample | All-offset Gaussian classification |
| [QuadraticArithmetic](../QCD.QuadraticArithmetic.001/lean/QuadraticArithmetic.lean) and [DyadicArithmetic](../QCD.QuadraticArithmetic.001/lean/DyadicArithmetic.lean) | Integral coordinate arithmetic and the stated dyadic formal identities | Every classification in the existing written quadratic study being formalized |
| [ComplexLattice](../QCD.ComplexLattice.001/lean/ComplexLattice.lean) | Actual integral quadratic ring, scalar-two guard and unique exact quotient, all-clock coordinate recovery, finite dyadic descent, both tail coordinates, injective complex embedding, full-sequence complex-norm escape for nonreal raw $`(3,c,2)`$ seeds with odd real $`c`$, and explicit residue-quotient cycles | Real-axis convergence or transfer of raw escape to a quotient convention |
| [ComplexCohomology](../QCD.ComplexCohomology.001/lean/ComplexCohomology.lean) | Ordinary period test and actual quotient isomorphism, ordered affine transport, common-potential reconstruction, and literal field-guard collapse | Lattice integrality or branch legality following from a field closing equation |
| [ComplexGraph](../QCD.ComplexCohomology.001/lean/ComplexGraph.lean) | Actual weak components, kernel isomorphism, and functional-graph incidence and cohomology dimensions over every field | An unmarked dimension distinguishing different cycle lengths |
| [ComplexLocalSystem](../QCD.ComplexCohomology.001/lean/ComplexLocalSystem.lean) | Actual twisted coboundary subspaces and quotient, neutral weighted-period isomorphism, homogeneous-potential isomorphism, and nonneutral zero dimensions | A useful universal local-to-global arithmetic criterion |
| [ComplexFields](lean/ComplexFields.lean) | Actual fields with 9 and 4 elements, Frobenius/conjugation, prime-subfield fixed points, all two algebra automorphisms, affine orbit transport and ramified nonfield controls | Raw Collatz halving descending to these finite quotients |
| [ComplexPolynomials](lean/ComplexPolynomials.lean) | Four explicit polynomials, selected finite-cycle values, complex derivatives and multiplier products, and exact exterior growth beyond radius 8 | Whole-integer interpolation, canonical QCD Julia sets, or certified pixel membership |

No `sorry`, substitute theorem axioms or unsupported theorem imports are used
in these owned modules. Standard classical/quotient axioms in Mathlib are
reported explicitly rather than described as axiom-free verification.

## Bounded computational contract

The atlas enumerates thirteen declared lattice families, each on all
$`97^2=9,409`$ coefficient seeds in $`[-48,48]^2`$: **122,317 seeds** altogether.
The raw/residue convention is part of every family record. The horizon is
256 ticks and the coordinate fence is $`2^{26}`$.

- A repeated **exact integer state** proves the recorded finite cycle.
- A checked odd transverse tail proves escape only for the specified **raw**
  scalar family. Each of the first four rows has 9,312 such seeds.
- A coordinate-fence exit is a numerical budget boundary, not a general
  divergence theorem.
- A remaining prefix is unresolved, not classified as bounded.

Each of the four quotient families reaches 45 cycles from this window,
with 745 cycle seeds, 8,510 coordinate exits and 154 unresolved prefixes.
Those are window-dependent counts, not complete cycle enumerations.
[AtlasData.json](other/AtlasData.json) retains the exact census and parameters.

The independent Go controls include signed exact division against rational
Gaussian elimination; dyadic entry bounds through rank 10; signed quotient
numerator recovery; exhaustive small local-system cochains; exact incidence
ranks over coefficient fields of characteristics 2, 3 and 5; finite-ring
inverses, roots and Frobenius laws; polynomial node checks; and a reused
workspace allocation check. Polynomial angular samples are floating-point
negative controls, not substitutes for the Lean exterior-growth proof.

Six polynomial views each contain $`256^2`$ samples: **393,216 floating-point
samples**, each with a 128-tick horizon and radius-8 exit test. There are four
polynomials, not six: two additional views resolve the otherwise invisible
plus-cycle basin near $`1`$, without changing any coefficient. Their declared
box is $`[0.994,1.006]+i[-0.006,0.006]`$. A fixed-mesh visibility test requires
zero survivors for the repelling zoom and a nonempty dark region for the
critical zoom. Dark pixels mean only that this test did not exit within the
budget. Numerical rounding, finite resolution and finite time prevent a
Julia-membership certificate.

## Visible assets and Markdown

The complex atlas generates nineteen vector PDFs and nineteen 300-dpi,
$`1500\times1500`$ PNG previews. The existing quadratic study generates seven
vector PDFs and matching PNGs. Thus the linked galleries contain **26
GitHub-visible PNG previews**, while PDFs remain ignored. Plots use Latin
Modern outline glyphs, explicit font sizes and the same font metrics for
layout and drawing; the mathematical-label handler supports its documented
finite subset, not arbitrary TeX.

`bash Scripts/CheckMarkdown.sh` checks maintained mathematical pages for
balanced dollar delimiters, legacy delimiters outside code, balanced TeX
groups/environments, problematic table pipes, local target/heading links and
PNG signatures. It handles math fences separately from executable examples.
This is a **static lexical check**, not MathJax execution, external-link
validation or a claim that every live GitHub page has been browser-tested.

## Tool versions recorded

- Lean 4.32.2, commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.
- Go 1.24.4, Linux/amd64; default checks use `CGO_ENABLED=0`.
- pdfTeX 1.40.29, TeX Live 2026/VoidLinux; latexmk 4.87; BibTeX 0.99e.
- Git 2.55.0; Python 3.14.7 for Markdown and inventory metadata checks.

## Post-push GitHub and MathJax checks

The checked batch was pushed to `origin/master` at commit `f9ca216` after the
separate formatting (`4d97f59`) and Markdown (`0cefb89`) commits. The remote
branch hash matched the local commit. The repository is private; an anonymous
page fetch returned GitHub's not-found page. Visibility was not changed.

Using the existing authenticated GitHub CLI, every one of the 75 committed
Markdown pages was rendered by GitHub's GFM API. Its output recognized 4,907
`math-renderer` expressions. Chromium 154.0.8037.57 then compiled all of them
with MathJax 3.2.2's full TeX-to-SVG component: **4,907 checked, zero errors**.
The audit decoded GitHub's extra HTML-entity layer inside math payloads; an
initial harness without that decoding reported 265 spurious `Misplaced &`
errors, all attributable to entity encoding rather than source mathematics.

That run established GitHub recognition and local compilation, but did not compare
rendered TeX with source TeX. A valid expression can compile after GitHub has silently
removed a backslash; zero MathJax errors therefore did **not** prove payload fidelity.
It was not a screenshot audit, a claim about GitHub's deployed MathJax version, or a
logged-in live-page layout check. Image readability has the separate inspection and
plotting contracts above. No credentials, generated HTML, browser profiles, PDFs or
TeX temporary files were committed.

## Subsequent source-to-GitHub payload repair

A later authentic API probe exposed punctuation loss in ordinary dollar-delimited
math. Maintained pages now use GitHub's protected inline form and `math` fences.
The repository-wide initial delimiter conversion preserved all ordered TeX payloads
and non-math projections. A second pass joined 25 physical row breaks in 24 formulas,
retaining the TeX row terminators, and moved one formula out of a nested list that
GitHub had parsed as ordinary code. This changed only two non-math indentation spaces.

The separate [payload checker](../Scripts/CheckGitHubMath.sh) compares source with
actual GFM output in count, order, display mode, and TeX. Fixed transport decoding is
mode-specific: one HTML DOM layer for both modes, and exactly one additional entity
layer for inline math. Literal-entity fixtures reject both under- and over-decoding.
The [payload regression suite](../Scripts/TestGitHubMath.sh) passed 13 accepted
fixtures and 18 payload negative controls, plus three accepted evidence cases and
eight cache-alias negative controls; the static suite passed its 15 negative controls.

The repaired publication scope contains **79 pages and 5,377 expressions**, including
the new residue-leakage family and intervening source-catalogue pages. Every payload
matched the source exactly after fixed transport decoding. Chromium 154.0.8037.57
compiled these exact inputs with MathJax 3.2.2: **5,377 checked, zero errors**.
All 24 row-layout pairs produced byte-identical SVGs with font caching disabled;
only the monotonically assigned context-menu counter differed in their containers.
The [residue-leakage verification ledger](../QCD.ResidueLeakage.001/Verification.md)
records the precise commands, conversion scope, safety repairs, and review dispositions.

These checks correct the missing fidelity obligation in the earlier 4,907-expression
run. They do not establish mathematical truth, verify the deployed GitHub MathJax
version, or substitute for a logged-in live-page visual audit.

## Independent review and migration checkpoint

Two initial read-only lanes completed the source-seam and Markdown audits;
their actionable definition, mathematical-summary and syntax findings were
repaired or explicitly quarantined in [ResearchAudit.md](ResearchAudit.md).
The two original final-gate lanes timed out while waiting for readiness with
`Subagent timed out after 1800000ms.` Their partial baseline observations are
**not** final approval. Both known lanes were recovered through the same
protocol after the readiness barrier. The independent semantic reviews
returned **OK with notes**, with no P0/P1 findings. They found two P2 issues:
the neutral twisted-dimension test did not require dimension one, and the
README attributed the fourth seed-$`3`$ failure value to a theorem checking
only the first three. The test now independently multiplies the edge
coefficients and checks both dimensions; the Lean theorem now checks all
four values. The code reviewer also identified the unresolved visual scale
in the global plus panels; two coefficient-preserving zooms address it.
Both targeted follow-ups confirmed the original issues resolved and found
no new mathematical or code blocker. They identified one remaining stale
TeX figure count, which was changed from seventeen to nineteen and the
affected document rebuilt. All reported findings have been addressed.

The code reviewer directly inspected ten original PNGs and reported no
obvious clipping, while noticing that the global plus basin was not visible.
The main agent additionally inspected the new critical zoom and corrected
ambiguous rounded tick labels. Reviewers inspected sources and supplied
build logs; they did not independently execute commands or validate live
GitHub rendering. This bounded review is not approval of the broad migration.

Twelve pre-work family directories remain untracked and outside this commit
batch. This explains the larger working-tree test and page counts above.
All 98 registered Lean source files are in the staged index, including the
nine modules in the Gaussian/quadratic/complex batch; the default build has
91 targets. An isolated staged-index checkout passed Go and Markdown checks
without borrowing any untracked family. Unrelated work was preserved, not
silently staged or discarded.

The remaining mathematical obligations include real-axis universal capture,
other complex parameter families, exhaustive infinite quotient basins,
a marked arithmetic local-to-global criterion, whole-integer entire-extension
formalization and a Julia-to-lattice transfer. The broad source inventory,
remaining formalizations and other migration tasks also remain open. See
[ResearchAudit.md](ResearchAudit.md) for precise source coverage and rejected
historical claims; no narrower task is presented as completion of the broader
goal.
