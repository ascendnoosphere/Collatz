<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Source catalogue: byte provenance and explicit coverage limits

**TL;DR:** the checked Go scanner inventories the included source files, reconciles
historical manifests, and hashes eligible ZIP payloads without executing source
programs. It preserves separate file and archive-occurrence identities. **This is
byte provenance, not a certificate of complete reading, mathematical correctness,
or completed result-level migration.**

The source is `/home/dell/collatz`; the maintained library is this repository.
The source remains read-only. The public evidence below was regenerated from that
source with [Inventory.go](go/Inventory.go), not copied from a success report.
Its five outputs agree byte-for-byte with the preceding private inventory.

## Checked repository update

The [repository audit](RepositoryAudit.md) records the new scalar-escape and
precision proofs, mathematical repairs, six bounded review lanes and freshly
executed repository checks. It distinguishes semantic coverage from build success.
The archive reader now binds member listings to a verified private snapshot with
explicit byte/output/time budgets. The new fixtures passed, but **the historical
production census below was not rescanned in this update**; its numbers retain
their original evidence scope. Ancestor-path hardening and multi-file output
transactionality remain limitations.

## Executed finite scope

| Quantity | Checked result |
| --- | ---: |
| Included current regular files / bytes | 2195 / 741878656 |
| Distinct SHA-256 digests | 2125 |
| Duplicate digest groups / additional copies | 32 / 70 |
| Original active / external records | 918 / 53 |
| Original records with declared byte changes / modification records checked | 9 / 16 |
| Current ZIP archives / file occurrences | 11 / 1627 |
| ZIP payload bytes fully hashed and CRC-checked | 280437001 |
| ZIP file occurrences matching current-file digests | 1472 |
| Current 7z archives / file occurrences / directory entries | 1 / 1491 / 99 |
| Earlier tree catalogue unchanged / added / changed / missing paths | 2147 / 48 / 0 / 0 |
| Earlier export unchanged / changed / missing workspace paths | 1453 / 33 / 0 |

All 1627 current ZIP occurrences in this scan were eligible regular files and
were hashed. The scanner also records excluded or nonregular entries when present;
its fixtures exercise those cases. The 1491 7z file occurrences were **listed from
headers only**: their payloads were not independently hashed or CRC-checked.
The combined current archive ledger contains 3217 records, including the 99 7z
directory entries. Matching a ZIP payload to a current-file digest identifies
matching bytes, not an additional independent proof or a reviewed result.

The original manifest has 971 records: 918 active and 53 external. The earlier
tree comparison accounts for all 2195 current paths as 2147 unchanged plus 48
added. The export comparison has a different historical scope: 1486 workspace
paths, of which 1453 are unchanged and 33 changed. Historical hashes are retained
rather than replaced by current hashes.

## Public evidence

- [CurrentArtifacts.json](other/CurrentArtifacts.json): every included current
  path, byte count and SHA-256 digest. Equal-byte copies retain separate identities.
- [OriginalArtifacts.json](other/OriginalArtifacts.json): original provenance and
  current evidence. A declared repair is not assumed semantically equivalent.
  Historical refreshed-bytecode digests remain separate from original digests.
- [ArchiveMembers.json](other/ArchiveMembers.json): archive path and digest,
  member name, occurrence number, size, recorded CRC, inspection tier, and any
  independently hashed payload digest and matching current paths. A recorded 7z
  CRC is header metadata, not an executed checksum verification.
- [HistoricalArchiveMembers.json](other/HistoricalArchiveMembers.json): records
  of unavailable historical archives. These are metadata, not accessed payloads.
- [Reconciliation.json](other/Reconciliation.json): exact counts, path-set deltas,
  declared modifications, exclusions, and limitations.

Archive occurrences are identified by archive path, member name and occurrence
number; equal member names do not overwrite each other. Current file paths are
not merged merely because their digests agree. No reading or theorem status is
inferred from an equal digest.

## Reproduction and input contract

Run from the repository root with Go 1.24.4 or later and `7z` on `PATH`:

```sh
export PATH="$HOME/.local/go/bin:$PATH"
CGO_ENABLED=0 go test -count=1 ./Library.SourceCatalogue.001/go
CGO_ENABLED=0 go vet ./Library.SourceCatalogue.001/go
make go GOFILE=Library.SourceCatalogue.001/go/Inventory.go
```

The scanner requires the following historical metadata below the chosen source
root; it is not a manifest-free scanner for arbitrary directories:

```text
artifacts/organization/original-file-manifest.json
artifacts/organization/source-modifications.json
artifacts/organization/tree-catalog.json
artifacts/organization/zip-members.json
artifacts/exports/collatz-progress-20261002T231927Z.manifest.json
```

To use a different source snapshot or output directory, invoke the same program
with explicit arguments:

```sh
CGO_ENABLED=0 go run Library.SourceCatalogue.001/go/Inventory.go \
  -source /path/to/read-only/corpus -output /path/to/evidence \
  -workers 4 -max-member 268435456 -max-archive 1073741824
```

The default output is `Library.SourceCatalogue.001/other`. Source programs,
embedded archive programs and external recovery paths are never executed or
opened as programs. The system `7z` decoder is used only to list current 7z headers.
The inventory does not extract archive members into the filesystem.

## Safety and verification

The scanner uses the Go standard library. Disjoint hashing chunks use independent
working buffers. Discovery does not follow symlinks or read nonregular leaves.
It records excluded `.git`, `.pi`, `.lake`, `__pycache__` and `target` directories.
Metadata is opened through a rooted, component-by-component identity check that
rejects symlink ancestors or leaves, excluded aliases and nonregular leaves.
Unknown original-record fields are retained under `additional_historical_fields`.
Reconciliation rejects repeated current, original, modification, historical
catalogue and export-workspace paths instead of silently collapsing them in maps.
A declared modification must name a present current artifact, even if its claimed
digest is empty. Archive occurrences are different: repeated member names remain
separate, numbered records.

Unsafe archive paths, links and explicitly excluded archive payloads, including
`Paper.pdf`, are recorded without consuming their payloads. Eligible ZIP payloads
are read fully within a default 256 MiB per-member and 1 GiB aggregate budget.
The same streaming pass computes SHA-256 and IEEE CRC, and every recorded ZIP CRC
is compared unconditionally, including zero values and members without a data
descriptor. Exceeding a budget is an error, not silent omission. The output location resolves
existing ancestors and rejects the source root and locations beneath it, including
source aliases reached through symlinks.

[Inventory_test.go](go/Inventory_test.go) has 14 focused tests covering discovery
exclusions, hashing and duplicate paths, archive occurrence identity, byte matching,
CRC corruption including a zero recorded CRC without a data descriptor, legitimate
empty payloads, checksum reset, both byte budgets, malformed 7z headers,
sorted historical deltas,
metadata traversal and trailing JSON, preservation of historical fields,
declared versus undeclared modifications, six corrupt path-identity controls,
external metadata, and source-output aliases. These tests and the full finite scan
passed with Go 1.24.4 on Linux;
7z header listing used 7-Zip 26.03. Verification of new public documentation and
independent review are recorded in [Verification.md](Verification.md).

## What remains open

**Artifact-level reconciliation and result-level migration are different obligations.**
A file can contain several claims; several files can be versions or formats of one
claim. The `result_assignment` fields in this byte ledger deliberately remain
pending where no separate checked semantic assignment is attached. Pending is not
an exclusion, a no-result disposition, or a downgrade of a supported source result.
The [root result catalogue](../README.md) links the existing mathematical families;
[the foundations](../Foundations.Main.StartHere/README.md) state their map and clock
conventions. Neither substitutes for the unfinished exhaustive source-to-result
crosswalk.

Remaining work includes reconciled reading coverage, distinct-claim extraction,
version and duplicate dispositions, checked dependencies, and destinations for all
relevant claims, historical experiments, archive-only material and cited research.
The byte scan does not close those obligations or resolve universal Collatz targets.

The scanner assumes a quiescent source, not an atomic or adversarially changing
filesystem snapshot. Archive containers are reopened after the initial hash pass.
Each JSON replacement is atomic, but the five-output publication is not
transactional. External archives are metadata-only, and 7z-to-ZIP payload equality
remains unchecked. These limits apply even when every command exits successfully.
