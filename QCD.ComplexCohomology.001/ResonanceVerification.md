<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Marked-cycle resonance — verification ledger

## Scope and status

**Parent formal and focused computational gates:** PASS for the result below.
**Independent publication review:** PASS for the bounded scope below; both accepted
corrections are closed. **Publication-snapshot and rendering checks:** PASS for the
executed snapshot below. Neither a build nor a source-audit report substitutes for
the independent publication reviews.

This batch adds the [marked-cycle result](Resonance.md), its Lean/Go/TeX files,
three reproducible figures, the [seven-row cycle-source audit](CycleSourceAudit.md),
and the [38-row analytic-source crosswalk](../QCD.ComplexAtlas.001/CanonicalClaims.md).
It also connects them to the existing catalogue and adds one default Lean target.
It does **not** complete the source migration, publish the twelve unrelated locally
untracked families, classify all generalized Collatz orbits, or prove a
Julia-set-to-arithmetic transfer.

The source audits inspect `/home/dell/collatz/FINALEE.MD` without modifying it.
Its SHA-256 is
`5d62b3352f77a89bf0d29b296c31b1b13f7d3cac04b300cd8dcc8f5e6a5dd569`.
Historical destination line references in those audits are explicitly tied to baseline
commit `6fdf2f0c14c1f74ad8c06cfc527ff658edda6fab`, not asserted to be current line numbers.
The source-audit reviews preceded this batch and are not its publication reviews.

## Formal result and recovery

Executed from the repository root:

```sh
make lean
lake env lean .pi/Research/ResonanceAxioms.lean
```

Lean **4.32.2**, release commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`,
checked the full default build: **94 default targets**. This is a target count,
not a count of audited source claims. The axiom script prints every one of the
**51 owned theorem declarations** in
[CycleResonance.lean](lean/CycleResonance.lean). An executed set-equality check matches
that list against the file's theorem declarations; every reported dependency set
is contained in `propext`, `Classical.choice`, and `Quot.sound`. There is no
`sorry`, admitted goal, or new axiom in this module. The audit script and logs are
private reproducibility diagnostics, not tracked proof artifacts.

The principal checked obligations are:

- `RawEdges`, `RawCycleOrbit`, `RawCycleReturn`, and `RawCycleMinimal` prove the legal
  integer cycle has exact period eighteen in the **original raw clock**.
- `WordHolonomy`, `PowerDefect`, and `NeutralIff` prove the seven affine and eleven
  division multipliers are neutral exactly when the integer defect vanishes in the
  coefficient field, with nonzero two required for halving.
- `ActualOffsetsExact` and `ActualOffsetClassZero` recover one periodic vertex
  potential. The actual dynamical offset is a **zero class**, including at resonance.
  `UnitPeriod` and `UnitClassNonzero139` separately exhibit a nonzero resonant class.
- `ResonantDimension`, `ControlDimension`, and `ComplexDimension` concern the existing
  genuine quotient of edge cochains by twisted coboundaries. They do not replace
  that quotient by an independently named one-dimensional space.
- `Gaussian139NoRoot`, `Gaussian139Card`, `Gaussian139Frobenius`, and
  `Gaussian139IsGalois` concern the actually constructed quadratic **field** extension.
  `Gaussian139Galois` and `Gaussian139Nontrivial` exhaust its two distinct base-field
  algebra automorphisms.
- `SigmaCoboundaries` proves descent of the semilinear edge action to the same quotient.
  `SigmaH1Period`, `SigmaH1Square`, and `SigmaH1NotLinear` check intertwining,
  involutivity, and the failure of extension-field linearity.
- `FixedPeriodEquiv`, `FixedH1Card`, and `Gaussian139H1Card` count classes via proved
  bijections, not an enumeration of all eighteen-edge cochain representatives.
- `FixedPartFixed`, `AntiPartNegative`, `GaloisDecomposition`, and
  `GaloisDecompositionUnique` reconstruct **the same class** uniquely from its fixed
  and sign parts. `Gaussian139Norm` proves the exact algebraic color invariant.

The raw branch guard remains integer divisibility. Reducing **coefficients of an
already legal ordered word** is not a claim that the guarded integer dynamics descends
modulo the resonance prime. Existing linter warnings in older modules remain; this
module built successfully.

The default build and all 51 theorem axiom checks passed again after review.
Private final executed logs: `.pi/Research/ResonanceFinalLean.log` and
`.pi/Research/ResonanceFinalAxioms.log`.

## Exact Go execution

Executed with Go **1.24.4**, `CGO_ENABLED=0`:

```sh
CGO_ENABLED=0 go test -count=1 -v ./QCD.ComplexCohomology.001/go
CGO_ENABLED=0 go vet ./QCD.ComplexCohomology.001/go
make go GOFILE=QCD.ComplexCohomology.001/go/CycleResonance.go
```

All **ten focused tests** passed. Formatting and focused vet passed. The generator
regenerates [CycleResonance.json](other/CycleResonance.json) and the three figures.
Its exact finite report records:

| Quantity | Control characteristic 137 | Resonance characteristic 139 |
|---|---:|---:|
| Word holonomy | 79 | 1 |
| Actual offset period | 44 | 0 |
| Last-edge unit period | 1 | 1 |
| Twisted-incidence rank | 18 | 17 |
| Quotient dimension | 0 | 1 |
| Actual offset exact | true | true |

The nonneutral period **44 is intentional**: exactness forces a zero weighted period
only under neutral holonomy. Both fields use the same eighteen legal integer states,
seven affine ticks, eleven division ticks, and integer power defect **139**.

The independent Gaussian-extension census checks all **19,321 coefficient pairs**:
19,321 Frobenius images, **139 fixed elements**, **two defining-polynomial roots**,
**19,320 nonzero inverses**, and 19,321 norm-identity/invariance checks. Multiplication
is quadratic field multiplication, not componentwise multiplication of a product.
The four goroutine chunks have disjoint counters and image-mark buffers; a
`sync.WaitGroup` joins them before aggregation. Finite elimination reuses a `Workspace`;
zero allocation in the tested rank loop is checked, not asserted for plotting or all
program operations. Invalid characteristics and out-of-word inputs are rejected.

Tests also check the affine prefix identity at every marked tick, conjugation versus
componentwise powering, a semilinearity counterexample, norm colors, the eight
supported mathematical labels, explicit glyph sizes, and unsupported-label rejection.
Neither finite enumeration nor a picture supplies the universal Lean proofs.

The **exact Git index export** also passed `CGO_ENABLED=0 go test -count=1 ./...`
and `CGO_ENABLED=0 go vet ./...` for **60 publication-snapshot packages**. That export
contains only indexed files, including the new checker, and excludes all twelve
unrelated untracked families. It is narrower than a test of the full local working tree.
No package from those unrelated families is being accepted for publication.

The corrected indexed checker passed the same 60-package test/vet gate again after
the accepted plotting correction. Private executed logs:
`.pi/Research/ResonanceGoTests.log`, `.pi/Research/ResonanceGoVet.log`,
`.pi/Research/ResonanceRun.log`, `.pi/Research/ResonanceFinalSnapshotGoTests.log`,
and `.pi/Research/ResonanceFinalSnapshotGoVet.log`.

## Paper and figures

Executed:

```sh
make tex TEXFILE=QCD.ComplexCohomology.001/tex/CycleResonance.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```

The paper compiled with pdfLaTeX/BibTeX/`amsalpha` to **nine letter-paper pages**.
The final compiler pass had no overfull boxes or undefined reference/citation warnings.
It retains the template's Computer Modern, approved packages, theorem numbering,
empty author field, and `\date{\today}`. The bibliography supplies Lang's algebra
reference. The inspected local source paths, ranges, SHA-256, and historical destination
baselines are recorded in `CycleSourceAudit.md` and
`QCD.ComplexAtlas.001/CanonicalClaims.md`, not in that bibliography.

The Go figures have vector PDF output and **300-dpi** PNG previews: **1500 × 1500**
for the square coefficient panel and **1800 × 1200** for each 3:2 word/offset panel.
The outlines use Latin Modern, with title/axes/ticks/scatter sizes **16/14/12/4 pt**.
The label handler supports exactly the **eight documented expressions**; it is not a
general TeX parser. Measurement and drawing use the same selected font metrics.
The parent inspected all three PNGs; this is not an independent live GitHub layout audit.

The coefficient panel displays a chosen system of integer representatives and the
algebraic norm. It does not equip a finite field with a canonical Euclidean metric,
plot a Julia set, or measure a fractal dimension. The other panels distinguish the
actual integer return from its nonneutral multiplier and the compensating affine offset;
floating logarithms are illustrations of exact separately checked data.

Both ignore scripts passed after the TeX builds. PDFs and compiler temporaries are
ignored; that paper's temporaries were removed by the Makefile. No PDF, hidden directory,
browser profile, or private diagnostic log belongs to the publication batch.

## GitHub transport and local math typesetting

The static checker, its regression suite, and the payload regression suite passed again:

```sh
bash Scripts/CheckMarkdown.sh
bash Scripts/TestMarkdown.sh
bash Scripts/TestGitHubMath.sh
bash Scripts/CheckGitHubMath.sh --output .pi/Research/ResonanceFinalGFM
```

The last command selected all **83 maintained publication-scope Markdown pages**
from the index. GitHub's authenticated GFM API returned all **5,907 expressions**
with exact agreement in count, order, inline/display mode, and TeX payload.
At baseline commit `6fdf2f0c14c1f74ad8c06cfc527ff658edda6fab`, the previous 79 pages
contained **5,377 expressions**. The executed baseline comparison checks source
SHA-256 and exact payload equality for all **76 unchanged pages**; each of the three
expanded README files retains its entire old formula sequence in order.

Chromium **154.0.8037.57** executed MathJax **3.2.2** on the exact decoded API payloads:
**5,907 compiled, zero errors**. The four display-layout repairs joined physical
lines after literal TeX row terminators. Their actual before/after SVGs are
**byte-identical**, with font caching disabled; the surrounding containers are also
identical after removing only the monotonically assigned `ctxtmenu_counter` attribute.
No TeX payload or SVG node was normalized to obtain that comparison.

The API gate proves payload preservation for these selected inputs. Local MathJax
execution proves compilation and the four stated rendering identities. Neither is
an audit of GitHub's deployed MathJax version or logged-in live-page layout; neither
proves mathematical truth. No credentials, generated HTML, or browser profile is tracked.
The final API receipt preserves exactly the same 5,907 payloads as the executed MathJax
run. Private executed evidence: `.pi/Research/ResonanceFinalGFM/MathPayloads.json`,
`.pi/Research/ResonancePayloadPreservation.json`,
`.pi/Research/ResonanceFinalPayloadIdentity.json`, and
`.pi/Research/ResonanceMathJaxResult.json`.

## Independent review and publication snapshot

Two fresh-context, read-only reviews completed: mathematical/Lean/TeX semantic
correspondence, and Go/figure/source-provenance/publication scope. Both returned
**OK with notes**, with no P0/P1 finding. They inspected the supplied execution logs;
they did not independently rerun the build or test commands. The parent remains sole
writer. Private review artifacts are `ResonanceReview/Mathematics.md` and
`ResonanceReview/ComputationAndScope.md` from workflow
`c48f5077-5b1a-408b-afe3-a788f93a5038`.

Accepted corrections:

- Both reviewers found that this ledger wrongly attributed local-source provenance
  to the bibliography. The corrected paragraph identifies Lang's algebra citation
  and locates source-snapshot provenance in the two source crosswalks.
- The computation reviewer found that the final legend entry overlapped the finite-field
  grid. Increasing the top plotting limit from `99.5` to `119.5` separates the full legend
  from all 19,321 cells. The parent regenerated and inspected the PNG, reran the focused
  Go tests/vet, and rebuilt the paper. The arithmetic JSON and the other two PNGs remain
  byte-identical. The retained computation reviewer independently inspected the new
  PNG and corrected provenance paragraph and confirmed **both findings closed**, with
  no regression found. Its final verdict remains **OK with notes** because command
  execution and whole-corpus coverage were not part of its review contract.

The retained follow-up resumed computation-review run
`7727c8ca-67ef-453a-a65b-06fb6bd12cec` as
`4e19ec23-674c-458c-a88c-370274cd391e`; the bound computation artifact now contains
that follow-up. Original review evidence is retained in the original run's logs.
The final publication batch contains exactly **17 selected paths**, with indexed
source bytes equal to working-tree bytes. No PDF, private diagnostic artifact, or
unrelated untracked family is included.

The whole-corpus inventory and claim crosswalk remain open. The 45 source rows are a
bounded audited contribution, not a declaration that every archived proof was read or
that every source claim has been migrated.
