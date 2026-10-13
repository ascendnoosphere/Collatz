<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Residue leakage — verification ledger

## Scope and publication status

**Parent execution:** PASS for the formal proof, exact finite checker, and paper
listed below. **Independent publication review:** READY with notes after four initial
reviews and two focused Markdown correction reviews. **Publication decision:** READY
for this scoped batch after the final index gates below. Commit and normal push follow
those gates and are recorded by Git history, not inferred from a receipt.
No receipt or successful build is being treated as independent mathematical approval.

This batch adds `QCD.ResidueLeakage.001`, its root catalogue entry, and two default
Lean targets. It does not publish any of the twelve pre-existing untracked research
families, complete the corpus-to-result crosswalk, classify the zero-density exceptional
set, or prove classical Collatz convergence.

Primary source: `/home/dell/collatz/FINALEE.MD:2019–2023`, Theorem 9.34,
SHA-256 `5d62b3352f77a89bf0d29b296c31b1b13f7d3cac04b300cd8dcc8f5e6a5dd569`.
The source is read-only. Its first-division convention and positive density domain were
checked directly. The proof retains the signed library's division-first convention by
`RawCast` and `IterateCast`, not by replacing a negative divisor with its absolute value.
The nonvacuous density antecedent $`1\le m<D`$ itself forces $`D\ge2`$.

## Formal verification

Executed from the repository root:

```sh
make lean
lake env lean .pi/Research/ResidueLeakageAxioms.lean
```

- Lean **4.32.2**, release commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.
- The full default build passed: **93 default targets**, including `ResidueCylinders`
  and `ResidueDensity`, with 2,657 dependency/build jobs in the executed invocation.
  These are build-target counts, not counts of mathematical source claims.
- The axiom audit printed **all 113 owned definitions/theorems** in the two new modules.
  Every printed dependency set is contained in `propext`, `Classical.choice`, and
  `Quot.sound`. There is no `sorry`, admitted goal, replacement axiom, or infinite
  predicate computed by a finite search.
- The exact finite-window bridge is proved in `HitDelayBound`, `RunRawBudget`,
  `DivisionCountMono`, and `SurvivesRawWindow`: a legal depth-$`h`$ prefix has a raw
  witness at a time between $`h`$ and $`mh`$, and survival is equivalent to at least
  $`h`$ divisions in the first $`mh`$ raw events.
- The original positive interval $`[1,X]`$ is preserved in
  `PositiveInfiniteBelowMinBound` and `PositiveInfinitePowerBound`. The latter includes
  the exact exponent $`\log m/\log D`$, its geometric-scale recovery, and $`m=1`$.
- `PositiveResidueDensityZero` and `PositiveFiniteDensityOne` prove the ordinary
  full-sequence limits. `FiniteDivisionsFormula` and `ResidueEscape` recover the same
  orbit in the full raw clock. `BoundedInfinite` and `PeriodicInfinite` exclude
  bounded/eventually periodic positive orbits from the affine-escape complement.
- `PeriodNeedNotDivideModulus` is a common-witness counterexample to the source's
  stronger return-order claim, not an assumption or an unresolved theorem.

The full build retains pre-existing linter warnings in unrelated modules; the new
modules built successfully. Private executed logs: `.pi/Research/ResidueLeakageAllLean.log`
and `.pi/Research/ResidueLeakageAxioms.log`. These logs are not tracked publications;
the committed sources and reproduction commands are the public evidence.

## Exact Go execution

Executed with Go **1.24.4**, `CGO_ENABLED=0`:

```sh
CGO_ENABLED=0 go test -count=1 -v ./QCD.ResidueLeakage.001/go
CGO_ENABLED=0 go vet ./QCD.ResidueLeakage.001/go
make go GOFILE=QCD.ResidueLeakage.001/go/ResidueCylinders.go
CGO_ENABLED=0 go test -count=1 ./...
CGO_ENABLED=0 go vet ./...
```

All **eight focused tests** passed. The full working-tree test and vet invocations
passed for **65 locally present packages**. This working-tree scope includes six
packages from pre-existing untracked families and is not the narrower publication
snapshot or approval of those unrelated families. The two new Go files were formatted
with `gofmt`; their owned lines and the new Lean lines are below 100 characters.

The regenerated [ResidueCylinders.json](other/ResidueCylinders.json) records:

| Quantity | Executed count |
|---|---:|
| Unit parameter models | 132 |
| Recorded model/depth rows | 660 |
| Legal parent classes | 75,490 |
| Independent accepted/rejected parent/child raw-clock comparisons | 898,742 |
| Shared-parent high-digit lift comparisons | 589,658 |
| Rows with strict period shortfall | 535 |

The recorded ranges are $`2\le q\le8`$, $`2\le D\le9`$, $`0\le c\le3`$, and
$`0\le h\le4`$. Every legal parent also checks all $`D`$ high digits at depth $`h+1`$.
These are repeated finite seed/depth comparisons, not that many distinct infinite
orbits. Zero offsets are algebraic controls; the public escape theorem keeps $`c\ge1`$.

The checker uses exact `math/big` arithmetic, explicit modulus/bit budgets, reusable
buffers, disjoint goroutine chunks, and stable record order. Tests cover rejected
inputs and child-level budgets, immediate/consecutive divisions, a rejected residue,
a 256-bit shift, closed/half-open interval ceilings, deterministic parallel assembly,
and zero allocations in the **tested** hot loops. Budget failure returns an error;
no row is silently skipped. Neither the report nor any test decides the infinite
predicate or supplies the universal density proof.

Private executed logs: `.pi/Research/ResidueLeakageGoTests.log`,
`.pi/Research/ResidueLeakageRun.log`, `.pi/Research/ResidueLeakageAllGoTests.log`,
and `.pi/Research/ResidueLeakageAllGoVet.log`.

## Paper and rendering

Executed:

```sh
make tex TEXFILE=QCD.ResidueLeakage.001/tex/ResidueLeakage.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```

The paper compiled with pdfLaTeX/BibTeX/`amsalpha` to an **eight-page letter-paper PDF**.
The final compiler pass had no overfull boxes and no undefined reference/citation
warnings. The last page was inspected as a raster preview, and PDF text was extracted.
This is not a claim that every page received an independent visual review.
The template's Computer Modern, approved package list, theorem numbering, title,
empty author field, and `\date{\today}` were retained. The source reference identifies
an inspected corpus snapshot; it does not invent an original author, composition date,
arXiv identifier, or public availability.

Both repository-wide PDF/TeX-temp ignore checks passed after each executed TeX build.
The generated PDF is ignored, and the Makefile removed that document's temporary files.
No PDF, TeX temporary, hidden directory, or private log belongs to the publication batch.
Private compiler log: `.pi/Research/ResidueLeakageTex.log`.

## GitHub math transport and local typesetting

Executed after the repository-wide protected-delimiter and display-layout repairs:

```sh
bash Scripts/CheckMarkdown.sh
bash Scripts/TestMarkdown.sh
bash Scripts/TestGitHubMath.sh
bash Scripts/CheckGitHubMath.sh --output .pi/Research/ResidueLeakageGFM
```

After staging, the last command selected all 79 maintained publication-scope Markdown
pages, including this family's two new pages. It used the authenticated GitHub GFM API,
not an anonymous page fetch. The static checker passed **91 locally present pages**; its regression suite
passed an accepted fixture and **15 negative controls**. The separate payload suite
passed **13 accepted fixtures and 18 payload negative controls**, plus **three accepted
evidence fixtures, five pre-request alias controls, and three write-time alias controls**.
The evidence fixtures use a temporary fake repository and mocked API responses, not
real source files or network requests.

GitHub returned all **5,377 expressions on 79 publication-scope pages**, with exact
agreement in count, order, inline/display mode, and TeX payload after the fixed API
transport decoding. The HTML parser removes one DOM-entity layer; inline payloads
need exactly one additional transport decode, while displays need none. Literal
entity controls prevent a decode-until-equal rule from hiding a real mutation.

The earlier bare-dollar source syntax allowed GitHub preprocessing to consume TeX
punctuation. It is now protected by GitHub's backtick-inside-dollar inline form and
`math` fences. The initial conversion preserved every ordered TeX payload and the
non-math projection on all 79 pages. A second layout pass joined **25 physical row
breaks in 24 formulas**, retaining each literal TeX row terminator. It also moved
one display outside a nested list because GitHub had treated it as ordinary code.
Only two indentation spaces in that list's non-math projection were removed.
These are formatting changes, not theorem or computational-certificate changes.

Chromium **154.0.8037.57** then executed MathJax **3.2.2**, using the exact decoded API
payloads: **5,377 compiled, zero errors**. All 24 before/after row-layout pairs have
byte-identical SVGs with font caching disabled. Their surrounding containers are
also identical after removal of the monotonically assigned `ctxtmenu_counter`
attribute; no TeX or SVG node was normalized to obtain the comparison.

The API gate proves source-to-payload preservation for these inputs. Local MathJax
execution proves compilation and the stated pairwise rendering identity. Neither
proves mathematical truth, certifies GitHub's deployed MathJax version, or claims a
logged-in live-page layout audit. No credentials, generated HTML, browser profile,
PDF, or private log is tracked. Executed diagnostics are retained locally under
`.pi/Research/ResidueLeakageGFM`, `MarkdownProtectionCertificate.json`,
`MarkdownLayoutCertificate.json`, and `ResidueLeakageMathJaxResult.json`.

## Independent review and final snapshot

Four fresh, read-only reviews completed under the governed asynchronous workflow.
The parent read all four reports in full and remains the sole writer.

| Review | Inspected scope | Disposition |
|---|---|---|
| Mathematics | Both complete Lean modules, the paper, finite report, and the targeted source block | Ready with notes; no proof blocker found |
| Finite checker | Both complete Go files, all 660 report rows, formal raw-window bridges, and executed parent logs | Ready with notes; no checker blocker found |
| Source and scope | Thirteen assigned result IDs, primary corpus blocks, citation, paper, formal claims, and root entry | Ready with notes; no scope blocker found |
| Markdown transport | Payload implementation, negative controls, decoded API evidence, and rendering claims | Alias blocker and comment-parity bug closed; ready with notes |

The mathematical and source reviewers both found the same incorrect theorem name
in this ledger. It is corrected to `PeriodicInfinite`; the formal theorem itself did
not change. The reviews do not certify the entire source corpus, mathematical truth
from finite tests, unsupported nil-workspace use, or GitHub's deployed browser layout.
Reviewers inspected sources and parent evidence; they did not independently execute
the parent commands.

The Markdown finding was reproduced before repair in an isolated fake repository:
manifest-file, cached-HTML-file, and cached-family-directory aliases each changed an
external sentinel. The corrected checker rejects aliases in every existing output
component and validates all selected destinations before requesting pages. It rechecks
paths when writing and atomically replaces temporary files instead of truncating
hard-linked destinations. Executed negative controls reject all five pre-existing
alias cases before any mocked request, and all three aliases installed during a
mocked response before they can redirect a write. The ordinary output and two hard-link
controls preserve their external sentinels; temporary output files are cleaned.
These tests cover the stated alias cases, not a filesystem adversary concurrently
renaming ancestors between checks and operations. The post-repair authenticated API
run again preserved all 5,377 expressions on the 79 publication-scope pages.
The parent read the first focused follow-up report in full. The reviewer found the
initial P1 resolved within the advertised filesystem threat scope and no new issue.
It inspected the complete corrected scripts and snapshot copies, preserved initial
report, updated ledger, and all seven requested execution logs, without independently
running them.

The final parent audit then found a separate inline-comment guard gap: a percent sign
preceded by two backslashes is a TeX comment, not a literal percent. Replacing its
following newline by a space can consume the next mathematical term. The old
immediate-predecessor test accepted that mutated payload in an executed negative
control. The corrected test uses full backslash-run parity. The new even-parity
negative control fails before the repair and passes after it; a new odd-parity literal
percent control remains accepted. No current protected single-line formula needed a
change. The parent read the second focused follow-up report in full. It confirmed
that full parity closes the demonstrated acceptance bug, that the prior alias blocker
remains closed, and that no new P0/P1/P2 issue was found. This review read both complete
scripts, their refreshed snapshot copies, both ledgers, and the actual RED/GREEN and
latest Markdown/API logs. It did not independently execute commands or establish tree
hashes. Its Markdown-lane disposition is **READY with notes**, within the parser,
filesystem, and rendering limitations stated above.

The refreshed isolated index export excludes all twelve untracked research families;
its source tree matched the real index at creation. Post-repair execution passed
**59 Go packages**, full vet, byte-identical regeneration of the 660-row report, and the
default Lean build (**93 default targets; 100 library targets; 103 compiled modules,
including three template submodules**). Static Markdown checks passed on **79 pages**,
both regression suites passed, and the authenticated API again preserved **5,377
expressions**. The eight-page TeX paper and both ignore checks passed. Only dependency
packages were linked; the snapshot's owned build directory was real and compiled both
new modules. The initial post-build count check omitted the nested template modules;
the corrected count matches all 103 tracked Lean sources.

The final documentation refresh is followed by renewed static/regression/API checks,
source-byte and tree agreement, and inspection of the **89 intended staged paths**.
No path from the twelve untracked families, PDF, TeX temporary, hidden directory,
credential, or private log is part of this batch. The mathematical and executable
sources are unchanged by this final metadata refresh. The scoped commit and normal
push follow these gates; no broad-migration completion is claimed.

## Remaining scope

The source's conditional mean-slope, log-drift, and pressure formulations, negative-
divisor variants, other source artifacts, and exhaustive result-level reconciliation
are not declared complete by this family. Pending source assignments are not exclusions
or downgrades. The universal statements in this family follow from the formal recovery
and limit arguments; the finite census is independently checkable auxiliary evidence.
