<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Written and Lean correspondence

Status: **AUXILIARY PROGRESS**. This is a statement-level scope audit, not a
line-by-line formalization of the article. The four existing
ClassicalCoalescence Lean files and the added
[SwarmLemma.lean](../lean/SwarmLemma.lean) have different scopes.

## Existing ClassicalCoalescence formalization

The files are
[ClassicalCoalescence.lean](../../QCD.ClassicalCoalescence.001/lean/ClassicalCoalescence.lean),
[SecondBurst.lean](../../QCD.ClassicalCoalescence.001/lean/SecondBurst.lean),
[PairedTails.lean](../../QCD.ClassicalCoalescence.001/lean/PairedTails.lean), and
[TerminalConverse.lean](../../QCD.ClassicalCoalescence.001/lean/TerminalConverse.lean).
They use natural-number shortcut dynamics. A written result can have a
correct proof without being a theorem in these files; the table distinguishes
that case from a difference in formal hypotheses or conclusions.

| Written result | Formal interface and limit |
|---|---|
| Definition of the first residual $`\mathcal R`$ | `Residual` agrees, including positivity, oddness, the excluded factor three, and the modulo-four guard. |
| Four initial parent rules and their exhaustive cover | Written proofs only. No single Lean theorem states the cover or its recovery implication. |
| Inverse cylinders at 3 modulo 8 and 7 modulo 64 | `Inverse110`, `Inverse110Order`, and `Inverse111010` give the universal identities and order inequalities. |
| Five-letter descent at 11 modulo 32 | `FiveLetterDescent` gives the identity and strict decrease. The bound $`9p\le8n`$ for parameters at least one is not its conclusion. |
| Join at 79 modulo 128 | `CylinderJoin` gives the join, `SourceStates` gives the meeting point, and `CylinderOrder` and `CylinderNoDescent` give the order and prefix obstruction. |
| Prefix at 27 modulo 1024 | `ResidualCylinder` proves membership in $`\mathcal R`$; `ResidualCylinderJoin` gives the join. It does not state membership in $`\mathcal R_*`$. |
| Second-burst parents | `TwoThreeBurstParent`, `BurstJoin`, `TwoBurstOrder`, and `ThreeBurstOrder` give joins, clocks, positivity, decrease, and contractions. The displayed common endpoints and words are not all exposed in the conclusions. |
| Paired eight-letter tails | `TailOneRelation`, `TailTwoRelation`, and `TailFourRelation` prove the three guarded affine identities. `PairedThreeParent` and `PairedTwoParent` give uniform contracted joins. |
| Paired example cylinders | Their `Join` and `Endpoint` theorems give the identities. The `Residual` theorems establish $`\mathcal R_*\cap3\mathbb Z`$, not the stronger $`\mathcal R_{**}`$ membership proved in the article. |
| Eight-letter and seven other direct cylinders | `EightLetterDescent` and the seven `Direct*Descent` theorems give the universal endpoints, positive parents, and stated contractions. Words and raw-clock counts are written separately. |
| Twenty-one further direct cylinders | The `FurtherDirect*` theorems give all-parameter endpoint identities and $`4p<3n`$. Their conclusions do not list words, affine constants, or raw clocks. |
| Deep cylinders at 2075 and 27 | `DeepDirect2075` and `DeepDirect27` give the endpoints and contraction bounds; the raw clocks are written corollaries. |
| Further join at 111 | `FurtherJoin111` gives the join, decrease, and contraction. The common endpoint is proved locally, not included in its conclusion. |
| General dyadic lifting | `DyadicLift` gives the universal endpoint formula. It does not separately expose the whole parity-prefix word. |
| Terminal divisibility | `PowerDivisibility` and `ThreeValuation` include exponent zero, where both sides of the equivalence are false. |
| Terminal classification | `TerminalPrefixClassification` retains the endpoint exponent and works for initial odd-run lengths zero and one as well. First-arrival and unique-peak claims are written corollaries with the stronger hypothesis $`a\ge2`$. |

The last distinction is necessary: at $`a=1,u=1`$, the state two appears
at two times, and the first hit of one precedes the displayed terminal
clock. The stronger peak and first-arrival conclusions must not be applied
under the weaker Lean classification hypotheses.

## Added cylinder and repetition theorem

[SwarmLemma.lean](../lean/SwarmLemma.lean) uses namespace `SwarmAttack`
and integer affine data for each finite binary word. It proves:

- `CylinderCriterion`: for every natural seed, the word's parity guards
  hold exactly when its affine numerator is divisible by its denominator.
- `RepeatedWordCriterion`: for every natural seed, finite binary word, and
  natural copy count, the first copies are legal exactly when the corresponding
  denominator power divides the affine displacement.
- The intermediate composition, one-copy defect transport, odd-multiplier
  coprimality, and divisibility-cancellation lemmas needed for induction.

Empty words and zero seeds are included. For a word with positive length
and nonzero displacement, the article derives the maximal-copy count by a
2-adic valuation; that maximal-count formula is not a separate Lean theorem.
The file uses no `sorry`, custom axioms, or `native_decide`.

## Written results not claimed as Lean theorems

The complete residual definitions after $`\mathcal R`$, their natural
densities, the exhaustive smaller-parent cover, join recovery, strong
induction, termination, and logarithmic parent depth remain written proofs.
So do the bounded-depth obstruction and the terminal first-arrival and peak
corollaries. No Lean theorem in these files states universal classical
capture or the complete residual-recovery implication.

The paired-cylinder membership difference above is a formal-scope limit,
not evidence that the stronger written membership is false. Likewise,
a missing endpoint in one theorem may be supplied by a neighboring theorem;
it must be cited rather than silently attributed to the smaller statement.

## Verification provenance

The original audit ran `lake build ClassicalCoalescence`, inspected the
four existing files for placeholders and declarations, checked displayed
cylinders at parameters zero through 49, and recomputed displayed density
fractions. Those numerical checks were evidence, not proofs of universal
statements. The original audit recorded 48 `native_decide` base checks;
maintenance replaced them with `decide`. None of the current five files
uses `native_decide`. Executed `#print axioms` checks for `CylinderCriterion`
and `RepeatedWordCriterion` report only `propext`, `Classical.choice`, and
`Quot.sound`, with no trusted-compiler axiom.

The [folder README](../README.md) lists the current build and exact-test
commands. A successful build verifies the formal statements above, not the
unformalized density and residual-recovery arguments.
