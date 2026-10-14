<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Repository audit and checked research update

## Scope and evidence boundary

The starting tracked revision was `44d4687` on `master`. The audit inventoried
all tracked topics, divided semantic reading among **six read-only review
lanes**, and ran repository-wide build, test and documentation checks. The
parent applied the repairs and developed the new proofs. All six lanes
completed; none failed. The reviewed tree also contained twelve pre-existing,
untracked research folders, which were preserved and not published.

**This is not an attestation that every proof and every implementation was
semantically read in full.** Compilation, source reading, bounded computation,
formal statement checking and image inspection are distinct evidence. The
coverage ledger below identifies the important gaps. In particular, successful
Lean compilation does not verify commented-out declarations, automatically
match prose to statements, or classify arbitrary integer QCD trajectories.

## New closed obligations

1. **General scalar off-axis escape.** On every specified imaginary quadratic
   coordinate order, signed scalar parameters with independent
   $`\lvert q\rvert,\lvert d\rvert\ge2`$ and arbitrary real integer offset
   force full-sequence escape of every nonreal seed. Actual ring guards,
   unique quotients, coordinate iteration and complex-norm recovery are
   proved. [Complete written and Lean proof](../QCD.ComplexLattice.001/README.md).
2. **Shared-support and dependent controls.** Raw $`(12,0,18)`$ at
   $`\theta`$ divides every third tick forever and grows by eight per block.
   Raw $`(4,0,8)`$ has a primitive nonreal five-cycle. Prime-exponent minors,
   not merely gcd or prime support, separate these families.
3. **Dynamical conjugacy without ring identification.** Matching the two
   integer coefficients between quadratic orders preserves every scalar raw
   tick and return time, but generally fails to preserve multiplication.
4. **Fixed-precision obstruction.** For every $`q,c\in\mathbb Z`$,
   $`d\ge2,k\ge0`$, states $`0,d^{k+1}`$ agree modulo $`d^{k+1}`$ and
   their raw successors do not. Legal division instead transfers one higher
   precision to one lower precision.
   [Proof and 297-item schema crosswalk](../QCD.ProfileDrop.001/SchemaAudit.md).
5. **Cyclic phase assembly.** The corrected maximum-defect gap follows from
   the checked local congruence, one uniform bound on the complete cyclic
   phase family, endpoint closure and nonresonance.
   [PhaseRigidCycle and counterexample](../QCD.PhaseRigid.001/README.md).
6. **Signed repunit formulas.** The geometric-sum affine identity and
   repunit-modulus identity now cover integer offsets and integer starting
   residues, matching the written statement.
   [RepunitCell.lean](../QCD.RepunitDivisor.001/lean/RepunitCell.lean).

The six new atlas rows add **56,454** bounded lattice seeds to the historical
122,317, for **178,771** altogether. The theorem-backed classification and
coordinate-fence exits remain separate. Six new PNG previews bring the
complex atlas to 25 panels; the original census is retained separately.

## Mathematical and documentation repairs

| Topic | Defect or scope mismatch | Checked correction |
|---|---|---|
| [Residue access](../QCD.ResidueAccess.001/README.md) | Auxiliary affine residues were called the raw quotient and the zero-orbit was said to exhaust all seed residues. | Restrict to the affine zero-orbit and first-division access. Raw $`(3,1,4)`$ sends congruent 0 and 4 to different residues; raw $`(2,1,3)`$ has the zero-avoiding seed 2. No post-division quotient is inferred. |
| [Phase rigidity](../QCD.PhaseRigid.001/README.md) | A maximum gap was stated at every individual phase. | Use the maximum over one complete cyclic word. The checked $`1100`$ example at $`q=3,c=1`$ has individual defect $`2/7<2/5`$. Added the formal cyclic assembly and matching detailed proof. |
| [Repunit unit cycle](../QCD.Repunit.001/README.md) | Ring cardinality was confused with the length of a constructed unit-seed cycle. | The ring has repunit-sum cardinality; the exhibited unit cycle has k states. No all-seed classification is added. |
| [Repunit affine arithmetic](../QCD.RepunitDivisor.001/README.md) | Text allowed signed offset/residue; formal formulas used naturals. | Added `RepunitAffineClosedInt` and `RepunitAffineModIdInt`. |
| [Common-base escape](../QCD.CommonBase.001/tex/CommonBaseHighOffset.tex) | An inequality was attributed to the wrong multiplication. | Write the actual chain comparing the smaller power with the larger power before multiplying by the nonnegative magnitude. |
| [Core relations](../QCD.Relations.Core.001/tex/RelationsCore.tex) | A pigeonhole collision was propagated from the wrong time; total return formulas ignored floor outside accessibility. | Start the repeated tail at the collision's first occurrence; retain floor in the total map and prove core/entry inequalities for that map. |
| [Cycle relations](../QCD.Relations.Cycles.001/tex/RelationsCycles.tex) | Incorrect parity expansion and a false lower-bound comparison. | Correct the even multiple in the parity identity and the doubled positive comparison. |
| [Signed obstruction](../QCD.SignedReturn.008/tex/SignedReturnObstruction.tex) | The zero-modulus quotient was called the zero ring; shifted magnitudes were asserted increasing from the start. | The zero-modulus quotient is the integer ring; the shifted magnitudes are unbounded and eventually increasing. |
| [Uniform signed return](../QCD.SignedReturn.015/tex/SignedReturnUniform.tex) | Missing positive-exponent/logarithm boundaries, inaccurate floor/ceiling formulas, a two-tick descent and zero parity. | Add the positive exponent and zero-excess cases; restore exact floor/ceiling formulas, three-tick odd descent, zero-even case and correct periodic-tail witness. |
| [Homogeneous paper](../QCD.Homogeneous.001/tex/Homogeneous.tex) | Extra packages and section-reset theorem numbering violated the repository template. | Restore the permitted preamble, global theorem numbering and template proof environment. |

### Refuted review finding and a real verification boundary

A review reported two active declarations named `UniformReturnBound` in
[SignedReturnUniform.lean](../QCD.SignedReturn.015/lean/SignedReturnUniform.lean).
A fresh direct Lean run succeeded, and inspection showed that the later
occurrence is inside a large block comment. There is **no active declaration
collision**. The earlier API was retained rather than renamed on false evidence.

The actual boundary is important: the active declarations end with
`NegTwoOneFirstTwoBefore`; the large continuation beginning with `ZeroOffset`
is an **uncompiled historical appendix**. Its contents are not certified by
`make lean`. The Lean source and topic README now state that boundary explicitly.
Formalizing any uncompiled assertion requires separate semantic review and
moving a correct proof into active registered source.

## Go and infrastructure repairs

- **Finite-field elimination:** normalize matrix entries before elimination,
  validate rectangular shape, and bound the inverse search over the supported
  characteristics 2, 3 and 5. Negative and maximum-machine-integer rows,
  empty matrices and ragged matrices have regression controls.
- **Raw atlas arithmetic:** reject unsupported multiplication tables,
  coefficients outside $`[-2^{16},2^{16}]`$, and tick inputs outside
  $`[-2^{44},2^{44}]^2`$ before arithmetic. Raw numerators are below
  $`2^{62}+2^{16}`$ in magnitude under this contract. The production census
  still uses the stricter $`2^{26}`$ fence. Residue mode accepts only its
  declared scalar-two convention. Exact large signed boundary controls use
  independent arbitrary precision.
- **Prime-exponent helper:** reject zero/nonpositive factor inputs and unit
  divisors before the factor-removal loop.
- **Finite functional graphs:** reuse generation/position arrays and skip
  already completed components. The four fixed cycle decompositions remain
  unchanged. The complete Gaussian characteristic-three census goes from
  **64 to 6 allocations** and **6,128 to 952 bytes** per call. Gaussian
  characteristic two goes from 20 to 4 allocations; Eisenstein characteristic
  two goes from 21 to 5. These are small fixed-case allocation measurements,
  not a claim of zero-allocation census or asymptotic speedup. Timing runs
  used different concurrency/background conditions, so no speed ratio is claimed.
- **Archive provenance:** copy and hash the same source stream into a private
  snapshot and check its byte count and expected digest before reading ZIP
  members or 7z headers. A later source replacement cannot attach new archive
  bytes to the earlier digest. Snapshot size is capped at 1 GiB; listing output
  at 32 MiB; external listing runtime at two minutes. Same-size replacement,
  later mutation and byte-budget failures have regression tests.
- **Markdown:** check inline, full, collapsed and defined shortcut references.
  In a Git repository the index defines maintained pages and published assets,
  so ignored or untracked files cannot hide missing fresh-clone links. The
  standalone fixture remains usable without Git. Twenty-one negative controls
  include unpublished local targets.

Remaining catalogue hardening: ordinary `HashFile` and snapshot source opening
are not fully directory-anchored against every hostile ancestor replacement;
output replacement is atomic per file, not one transaction across the related
JSON files. Production external archives were not rescanned in this update.
The tests establish fixture contracts, not current corpus reconciliation.

## Semantic coverage ledger

The read-only lanes were fresh-context reviews. Their run identifiers are
retained here for provenance; they are not additional theorem axioms or
independent executions of commands they did not run.

| Lane | Run | Actual semantic coverage and limitation |
|---|---|---|
| Complex | `e00456fd-c8fd-41a6-ba87-af9b875b8a6d` | All 39 discovered text/source/data files in the five assigned complex topics, both JSON artifacts and 29 PNG previews. No new parent scalar proof or later edits were in that baseline review. No child Lean/TeX/test execution. |
| Positive families/reductions | `2b925024-35b6-4665-a44f-f18149054bd6` | Full 17 TeX proofs, 35 Lean sources, 17 Go implementations and 17 tests in its assigned foundations/family scope. Supporting README/BibTeX/data coverage was not uniformly complete. No child execution. |
| Binary topics | `d2903cbc-ecee-4b14-8655-565b7e854812` | Full statement review of 29 topic READMEs, full proof review of 15 TeX and 19 Lean files, and 7 bounded Go implementations. CarryGap was partial; 14 TeX, 10 Lean modules, 9 Go implementations and the assigned tests remained unread. |
| Signed/profile/core | `1358e275-4fe4-4d63-a6c5-8a1bc36dc090` | Most smaller signed-return/core/profile modules fully read; substantial portions of SignedReturnUniform, SignedReturnExamples and companions remained unread. The alleged duplicate declaration was independently refuted by the parent. |
| Go/infrastructure | `ee5a63bc-152f-4167-a1e7-324b350c1613` | Full semantic reading of 13 of 121 Go files, root infrastructure, six scripts and Templates; all-package tests and vet were executed. Much broader mechanical coverage is not full semantic reading. |
| Inventory/untracked | `796f13df-60df-470e-a8a4-9d67edb61738` | Repository/corpus inventory and selected statement/proof blocks. Archive/corpus metadata is not a proof audit. The twelve untracked topics were inspected selectively and preserved. |

Coverage overlaps: do not add these lane totals to claim a count of independently
reviewed files. Imported Mathlib, Go dependencies, the external corpus and
external papers were not fully semantically audited. The parent checked the
new theorem statements, proofs, recovery steps and repaired arguments, then
executed the validation below on the resulting working tree.

## Executed validation for this update

Run from the repository root:

| Command/operation | Observed result and scope |
|---|---|
| `make lean` | Passed all **96 configured default targets**, 2,741 build jobs; legacy linter warnings remain. ScalarEscape and ProfilePrecision are registered. |
| Fresh `lake env lean` of the new axiom audit | Passed **29 newly added theorem declarations**; only the standard `propext`, `Classical.choice`, `Quot.sound` axioms occur. The audit covers scalar escape/recovery, precision, cyclic rigidity and signed repunit formulas. |
| `CGO_ENABLED=0 go test -count=1 ./...` | Passed all **66 locally present Go packages**, including preserved untracked packages. This does not publish or semantically certify those untracked topics. |
| `CGO_ENABLED=0 go vet ./...` | Passed. |
| Fresh `make tex TEXFILE=...` batch | Passed all **75 previously tracked TeX documents plus ScalarEscape.tex**, 76 documents. Compile success is not proof correctness. |
| PDF and TeX-temp ignore scripts | Passed after the complete TeX batch. Generated PDFs/temps remain untracked and ignored. |
| `bash Scripts/TestMarkdown.sh` | Passed accepted fixtures and 21 negative controls, including missing/unpublished reference targets. |
| `bash Scripts/TestGitHubMath.sh` | Passed 13 accepted payload fixtures, 18 negative payload controls and the evidence/cache safety controls; this suite uses a mocked API, not live rendering. |

The final staged-index and live GitHub transport results are recorded in the
[complex verification ledger](../QCD.ComplexAtlas.001/Verification.md#scalar-and-profile-update).
Source-hash-specific transport success is not mathematical validation or
live-browser layout inspection. No credentials, private runtime transcripts,
PDFs, TeX temporary files or hidden directories are published.

## Topic organization

The existing domain-folder convention is retained. The general scalar theorem
is split from the quantitative dyadic-tail theorem **inside the same complex
lattice topic**: the general theorem is broader in parameters but weaker in
clock estimates. `ProfilePrecision.lean` is split from the expansion-specific
profile module because it has no expansion or hitting-time hypothesis.
The schema crosswalk consolidates the 297 proposed observables by actual
mechanism rather than creating a folder per label.

Safe further consolidations require interface work: affine word/conductor
foundations can be shared, but first-hit arithmetic, legal guarded recovery,
finite cores and all-seed classifications are different layers. Repunit
sources currently duplicate namespace-level names, so a literal import-based
merge without deduplication would be unsafe. Different gap observables should
share an index, not be identified as one defect. No mass move was used to
conceal an unchanged proof obligation.

## Remaining obligations

- Full semantic reading and statement/proof correspondence for the explicitly
  unread files; active versus commented-out formal scope in the large signed
  modules remains a priority.
- Universal integer-axis behavior, dependent scalar families with nonzero
  offset, nonreal offsets and nonscalar parameters are not classified by the
  new off-axis theorem.
- Complete infinite cycle/basin classifications of the residue-quotient maps,
  uniform quadratic-arithmetic formalization and the external corpus migration
  remain open.
- A branch-aware and clock-aware recovery mechanism through arbitrarily many
  divisions is still required for a general integer profile classifier.
  Static labels, finite searches and Julia pictures do not supply that bridge.

The next executable audit step is to review the unread binary proof companions
and the active large signed-return interfaces before promoting any historical
or necessary-condition statement to a complete formal classification.
