<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Executed verification and remaining obligations

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
| [ComplexLattice](../QCD.ComplexLattice.001/lean/ComplexLattice.lean) | Actual integral quadratic ring, scalar-two guard and unique exact quotient, all-clock coordinate recovery, finite dyadic descent, both tail coordinates, injective complex embedding, full-sequence complex-norm escape for nonreal raw $(3,c,2)$ seeds with odd real $c$, and explicit residue-quotient cycles | Real-axis convergence or transfer of raw escape to a quotient convention |
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
$97^2=9,409$ coefficient seeds in $[-48,48]^2$: **122,317 seeds** altogether.
The raw/residue convention is part of every family record. The horizon is
256 ticks and the coordinate fence is $2^{26}$.

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

Six polynomial views each contain $256^2$ samples: **393,216 floating-point
samples**, each with a 128-tick horizon and radius-8 exit test. There are four
polynomials, not six: two additional views resolve the otherwise invisible
plus-cycle basin near $1$, without changing any coefficient. Their declared
box is $[0.994,1.006]+i[-0.006,0.006]$. A fixed-mesh visibility test requires
zero survivors for the repelling zoom and a nonempty dark region for the
critical zoom. Dark pixels mean only that this test did not exit within the
budget. Numerical rounding, finite resolution and finite time prevent a
Julia-membership certificate.

## Visible assets and Markdown

The complex atlas generates nineteen vector PDFs and nineteen 300-dpi,
$1500\times1500$ PNG previews. The existing quadratic study generates seven
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
README attributed the fourth seed-$3$ failure value to a theorem checking
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
