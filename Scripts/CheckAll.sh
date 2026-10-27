#!/usr/bin/env bash
# SPDX-License-Identifier: CC-BY-4.0
# Run the source checks and builds available in a fresh checkout, from the repository root.
set -euo pipefail

Root="$(git rev-parse --show-toplevel)"
if [[ "$PWD" != "$Root" ]]; then
	printf 'run from the repository root: %s\n' "$Root" >&2
	exit 1
fi
export PATH="$HOME/.local/go/bin:$PATH"

# Formatting checks do not rewrite sources or include ignored dependency trees.
mapfile -d '' -t GoFiles < <(git ls-files -z '*.go')
Unformatted="$(gofmt -l "${GoFiles[@]}")"
if [[ -n "$Unformatted" ]]; then
	printf 'Go files need gofmt:\n%s\n' "$Unformatted" >&2
	exit 1
fi
for Script in Scripts/*.sh; do
	bash -n "$Script"
done
git diff --check

# The payload regressions are offline; the authenticated GitHub API check is separate.
bash Scripts/CheckMarkdown.sh
bash Scripts/TestMarkdown.sh
bash Scripts/TestGitHubMath.sh
CGO_ENABLED=0 go test ./...
CGO_ENABLED=0 go vet ./...
make lean
bash Scripts/CheckLeanImports.sh

# Figure generators locate outputs relative to their source file. Stage copies so that
# regenerating ignored vector PDFs cannot overwrite tracked previews or research data.
Workspace="$(mktemp -d)"
trap 'rm -rf "$Workspace"' EXIT
FigureSources=(
	QCD.ComplexCohomology.001/go/CycleResonance.go
	QCD.ComplexDynamics.001/go/ComplexDynamics.go
	QCD.QuadraticArithmetic.001/go/QuadraticArithmetic.go
)
for Source in "${FigureSources[@]}"; do
	mkdir -p "$Workspace/$(dirname "$Source")"
	cp "$Source" "$Workspace/$Source"
	make go GOFILE="$Workspace/$Source"
done
while IFS= read -r -d '' Pdf; do
	Destination="${Pdf#"$Workspace"/}"
	if ! git check-ignore -q "$Destination"; then
		printf 'generated PDF is not ignored: %s\n' "$Destination" >&2
		exit 1
	fi
	cp "$Pdf" "$Destination"
done < <(find "$Workspace" -type f -name '*.pdf' -print0)

# Build each tracked manuscript; check ignored outputs even when typesetting fails.
while IFS= read -r -d '' Document; do
	Status=0
	make tex TEXFILE="$Document" || Status=$?
	bash Scripts/CheckIgnoredPdfs.sh || Status=1
	bash Scripts/CheckIgnoredTexTemps.sh || Status=1
	if (( Status != 0 )); then
		exit "$Status"
	fi
done < <(git ls-files -z '*.tex')

printf 'Repository source checks and builds passed.\n'
printf 'These checks do not establish every written proof or live GitHub rendering.\n'
