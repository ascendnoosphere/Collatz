<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Historical baseline build record

Status: **AUXILIARY PROGRESS**. These commands tested the earlier state at
commit `2b1cb92b3faec3cf6a6f464ddb5e949353f75d03`, with the five
ClassicalCoalescence files modified and this folder untracked. They are
baseline results, not validation of later edits or proofs of capture.

## Recorded environment

The original run used Lean 4.32.2, Lake 5.0.0-src, Mathlib `v4.32.2`,
Go 1.24.4 on linux/amd64, and Latexmk 4.87 with pdfLaTeX. Go required
`$HOME/.local/go/bin` on `PATH`. The existing Mathlib build cache was reused.
The initial `go version` probe failed because Go was not on the shell's
`PATH`; the Makefile already supplied the correct path.

## Recorded checks

| Command | Result |
|---|---|
| `git diff --check` | No whitespace errors |
| `make lean` | Successful warm-cache build, 2780 jobs |
| `lake env lean QCD.ClassicalCoalescence.001/lean/ClassicalCoalescence.lean` | Source re-elaboration passed |
| `CGO_ENABLED=0 go test -count=1 ./QCD.ClassicalCoalescence.001/go` | 13 tests passed |
| `CGO_ENABLED=0 go test -count=1 ./QCD.ResidueLeakage.001/go ./QCD.LocalJoin.001/go ./QCD.InverseBudget.001/go ./QCD.DyadicDynamics.001/go` | Four packages passed |
| `gofmt -l` and `CGO_ENABLED=0 go vet` on those five Go packages | No findings |
| `bash Scripts/CheckIgnoredPdfs.sh` | Passed |
| `bash Scripts/CheckIgnoredTexTemps.sh` | Passed |
| `make tex TEXFILE=QCD.NagellList.001/tex/NagellList.tex` | Three-page build passed; temporary files cleaned |
| `latexmk -pdf -interaction=nonstopmode -halt-on-error ClassicalCoalescence.tex` on a temporary source copy | 29 pages; no undefined references or citations on the final pass |

The verbose Go run recorded 50 passing tests across the five packages:
13 ClassicalCoalescence, 11 ResidueLeakage, 4 LocalJoin, 13 InverseBudget,
and 9 DyadicDynamics. The working-tree status was unchanged apart from
this report. The temporary TeX build directory was not retained.

## Scope and trust

The baseline did not rebuild Mathlib from scratch, test all repository Go
packages, run the race detector, or verify the mathematical density and
residual-recovery arguments. The modified ClassicalCoalescence Lean file
was separately re-elaborated, so its result was not inferred solely from a
warm-cache build.

The original baseline recorded 48 `native_decide` base checks, with a
trusted-compiler dependency. Maintenance replaced those checks with `decide`;
the current four ClassicalCoalescence files contain no `native_decide`.
Their dyadic lifting theorems establish identities for every parameter, not
by sampling. The new [SwarmLemma.lean](../lean/SwarmLemma.lean) also uses
no `native_decide`. The cylinder and repetition theorems' printed axiom lists
contain only `propext`, `Classical.choice`, and `Quot.sound`.

The initial read-only treatment of the five modified files ended when their
completion was authorized. Current reproducible checks for this folder are
listed in its [README](../README.md); this report preserves only the
historical baseline.
