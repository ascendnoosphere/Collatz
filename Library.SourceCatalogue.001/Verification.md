<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Source catalogue verification

## Scope and completed execution

This record covers the new public byte-provenance scanner and its five JSON
outputs. It does not certify complete source reading or semantic migration.
The inspected source programs and archive programs were not executed.

| Check | Executed result |
| --- | --- |
| `CGO_ENABLED=0 go test -count=1 -v ./Library.SourceCatalogue.001/go` | PASS: all 14 focused tests, including six corrupt path-identity controls and the no-descriptor zero-CRC regression |
| `CGO_ENABLED=0 go vet ./Library.SourceCatalogue.001/go` | PASS |
| `make go GOFILE=Library.SourceCatalogue.001/go/Inventory.go` | PASS: fresh finite source scan |
| `gofmt -l` across all nonhidden working-tree Go sources | PASS: no formatting differences |
| `CGO_ENABLED=0 go test -count=1 ./...` | PASS: all 64 locally present Go packages |
| `CGO_ENABLED=0 go vet ./...` | PASS: all locally present Go packages |
| `bash Scripts/CheckMarkdown.sh` | PASS: 89 local pages, lexical math, links, anchors and PNG signatures |
| `bash Scripts/TestMarkdown.sh` | PASS: accepted fixture and ten intended negative controls |
| `git diff --check` | PASS |
| Fresh outputs versus earlier private inventory | All five files byte-identical |

The scan accounted for 2195 included current files, 741878656 bytes and 2125
distinct SHA-256 digests. It hashed and CRC-checked 1627 file occurrences across
11 ZIP archives, totaling 280437001 payload bytes; 1472 matched current-file
digests. It listed one 7z archive with 1491 file and 99 directory entries without
independently reading payloads. The combined current archive ledger has 3217 rows.
Historical comparisons retain 918 active and 53 external original records,
nine declared original-record byte changes and 16 checked modification records.

The commands used Go 1.24.4 on Linux/amd64 and 7-Zip 26.03. JSON comparison and
inspection-tier counts were checked from the generated evidence; they do not
constitute a new mathematical computation or proof review. The 64-package and
89-page counts include the twelve preexisting, untracked research families;
they are working-tree scopes, not the narrower publication snapshot.

The public scanner additionally rejects duplicate paths in reconciliation inputs
and declared modifications naming absent current artifacts. The six corrupt
controls exercise these failures rather than accepting overwritten map rows.
A fresh independent code review identified that Go's ZIP reader can skip comparison
of a zero recorded CRC when no data descriptor is present. The added regression
reproduced that defect before correction. The scanner now computes IEEE CRC in the
same bounded streaming pass as SHA-256 and compares every member's CRC unconditionally
before accepting or counting it. The regression, valid-empty and valid-nonempty
controls, repeated-read checksum reset, all 14 focused tests, fresh production scan
and all-package checks passed after correction. The finite production scan still
yields the same five JSON files.

## Review and final documentation gates

Three fresh read-only lanes inspected scanner correctness, public provenance and
possible next source-migration seams. The provenance review found no documentation
issue within its stated reading and metadata scope; it did not run the commands,
read every ledger row or certify a full sensitive-data clearance. The code review
initially blocked publication on the zero-CRC defect described above. Its retained
focused follow-up reread the complete implementation, tests, documentation and
refreshed execution records, closed that P1, and returned **OK with notes** with
no further issue found. The reviewer did not run the commands or independently
recompute all ledger rows. The source scout identified candidate obligations,
not newly verified mathematical results.

The parent inspected the staged batch: root `README.md` plus the nine catalogue
files only. No hidden files, PDFs, TeX temporaries or files from the twelve preserved
untracked research families were included. An isolated copy exported from that
Git index passed these narrower publication-snapshot checks:

| Publication-snapshot check | Executed result |
| --- | --- |
| `CGO_ENABLED=0 go test -count=1 ./...` | PASS: all 58 included Go packages |
| `CGO_ENABLED=0 go vet ./...` | PASS: all included Go packages |
| `bash Scripts/CheckMarkdown.sh` | PASS: 77 included Markdown pages |
| `bash Scripts/TestMarkdown.sh` | PASS: accepted fixture and ten negative controls |
| `git diff --cached --check` | PASS |

The final documentation update is checked again before publication; the commit
and normal push are separate Git operations recorded in repository history.
Static Markdown acceptance does not claim MathJax evaluation, external-link
validation or live GitHub rendering.

The earlier private scanner had independent review and focused repairs for
metadata symlink traversal and preservation of a historical bytecode digest.
That history is not substituted for independent review of this public batch.

## Residual obligations

- Source quiescence is assumed; this is not an atomic filesystem snapshot.
- Each output replacement is atomic, but the five-file publication is not a
  transaction. Archive files are reopened after initial container hashing.
- 7z CRC values are header metadata, not independently checked checksums;
  7z-to-ZIP payload equality remains unverified.
- Unavailable external originals and historical archive payloads were not accessed.
- Explicit exclusions remain exclusions, not reviewed source material.
- Equal digests and successful decoding do not prove a mathematical statement.
- The exhaustive artifact-to-result crosswalk, reading coverage, supported-result
  migration and dependency verification remain open.

The [catalogue README](README.md) specifies the input contract, reproduction
commands, exact safety boundary and pending-assignment semantics.
