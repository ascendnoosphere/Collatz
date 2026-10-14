<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Source index

The independent local corpus at `/home/dell/collatz` contains manuscripts,
notes, extracted papers, programs and historical variants. It is read-only
from this library. The maintained mathematical results are organized by
subject in the [root index](../README.md).

The following pages develop the relevant mathematics rather than treating
different source formats as independent proofs:

- [Integral cycle arithmetic](../QCD.ComplexCohomology.001/CycleArithmetic.md):
  cyclic cokernels, offset conductors and exact phase reconstruction.
- [Analytic extensions](../QCD.ComplexDynamics.001/AnalyticClaims.md):
  interpolation, parity coding and reciprocal compactification.
- [Complex-map literature](../QCD.ComplexDynamics.001/Literature.md):
  integral, residue-wise and continuous conventions.
- [Arithmetic profiles](../QCD.ProfileDrop.001/ArithmeticProfiles.md):
  domains and uses of single-state and pair observables.

## Catalogue utility

[Inventory.go](go/Inventory.go) locates current files, historical records and
archive occurrences without running source programs. The machine-readable
catalogue in [other/](other/) is a source-finding aid, not a theorem database.

Run from the repository root:

```sh
CGO_ENABLED=0 go test ./Library.SourceCatalogue.001/go
make go GOFILE=Library.SourceCatalogue.001/go/Inventory.go
```

A different read-only source and output directory can be specified explicitly:

```sh
CGO_ENABLED=0 go run Library.SourceCatalogue.001/go/Inventory.go \
  -source /path/to/corpus -output /path/to/catalogue -workers 4
```

The utility expects the original manifest, modification list, tree catalogue,
archive-member list and export manifest used by this corpus. It does not
scan an arbitrary directory without those inputs. The source tree should
remain quiescent during a run; output must be outside that tree.
ZIP inspection has explicit per-member and aggregate budgets.
7z inspection lists headers rather than establishing payload equality.
The five output replacements are not a single transaction.
[Tests](go/Inventory_test.go) exercise invalid paths, duplicate records,
archive occurrence identity, corrupt input and resource refusal.

Mathematical statements must still be checked against their definitions,
hypotheses and proofs. Source variants, PDF extraction and generated
summaries do not replace that work.
