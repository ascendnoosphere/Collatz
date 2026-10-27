<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Classical Collatz research audit

This folder contains nine workstream reports, one Lean proof, and an executable
Go checker. The original assignment listed twenty workstreams; reports for
the other eleven were not delivered and are not listed as completed work.

The target is that every positive integer reaches the shortcut cycle
$`1\leftrightarrow2`$, where

```math
T(n)=\begin{cases}n/2,&2\mid n,\\(3n+1)/2,&2\nmid n.\end{cases}
```

The [ClassicalCoalescence reduction](../QCD.ClassicalCoalescence.001/README.md)
gives every $`n>1`$ outside its explicit residual $`\mathcal R_{\mathrm E}`$
a positive smaller parent with a legal orbit join. Strong induction therefore
reduces capture to that residual. Its density is
$`6689147268412473047/315179916321896792064`$, about 2.12%.
Capture on the residual remains unproved. A smaller positive density alone
would not discharge that all-seed obligation.

## Checked additions

- [SwarmLemma.lean](lean/SwarmLemma.lean) proves the cylinder criterion and
  the exact repeated-word budget for every finite binary word, seed in
  $`\mathbb N`$, and repetition count. It includes empty words, zero seeds,
  and zero copies. The proof uses no `sorry`, new axioms, or `native_decide`.
- [SwarmChecks.go](go/SwarmChecks.go) checks 163,200 finite word/seed/count
  combinations and exhausts the proved cycle window for ranks six through
  nine. [The tests](go/SwarmChecks_test.go) also verify all 31 direct cylinders
  by exact affine-coefficient propagation, both legs of the new smaller-parent
  join, and corrupted-certificate controls. These local certificates do not
  prove a complete cover of the residual.
- [The cycle report](other/Agent11.md) proves the finite search window and
  records all 4,383 compositions examined. It withdraws the earlier rank-40
  and rank-1000 claims, which relied on an incorrect numerator estimate.

From the repository root, with Go on `PATH`:

```sh
make lean
make go GOFILE=QCD.SwarmAttack.001/go/SwarmChecks.go
CGO_ENABLED=0 go test -count=1 ./QCD.SwarmAttack.001/go
```

`SwarmLemma` is a default Lake target. The finite checks are supplementary;
the repeated-word theorem is proved in Lean for all its stated parameters.
The complete ClassicalCoalescence residual recovery and density arguments
remain written proofs, not Lean declarations.

## Reports

| Report | Scope |
|---|---|
| [01](other/Agent01.md) | Historical baseline builds and tests |
| [02](other/Agent02.md) | Exact residual density and disjointness arithmetic |
| [03](other/Agent03.md) | Lean/TeX statement correspondence and current formal scope |
| [04](other/Agent04.md) | Repository obligation map and open residual-parent step |
| [07](other/Agent07.md) | Dyadic cylinders and bounded finite-state descent obstructions |
| [10](other/Agent10.md) | Mixed-radix cylinders and the finite direct-cover obstruction |
| [11](other/Agent11.md) | Corrected exclusion of non-unit cycles at ranks six through nine |
| [13](other/Agent13.md) | Raw-map 2-adic coding and its capture-transfer limitations |
| [16](other/Agent16.md) | Retained exact uniform-cylinder checker and negative controls |

Report 01 preserves the historical baseline; report 03 includes the added
formal theorem. Temporary `/tmp/opencode` programs mentioned in historical
reports are not distributed artifacts. Only the retained source and commands
above are current reproducibility claims.
