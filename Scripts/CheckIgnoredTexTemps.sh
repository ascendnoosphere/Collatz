#!/usr/bin/env bash
# CheckIgnoredTexTemps.sh
# Recurse the repository. Every TeX temp must be gitignored.
# Temps: .log .aux .out .toc .fls .fdb_latexmk .synctex.gz .bbl .blg
# Exit 1 if any matching file is not ignored.

set -euo pipefail

Root="$(git rev-parse --show-toplevel)"
cd "${Root}"

Fail=0
while IFS= read -r -d '' Temp; do
	if ! git check-ignore -q "${Temp}"; then
		printf 'not ignored: %s\n' "${Temp}"
		Fail=1
	fi
done < <(find . -path './.git' -prune -o -type f \( \
	-name '*.log' -o \
	-name '*.aux' -o \
	-name '*.out' -o \
	-name '*.toc' -o \
	-name '*.fls' -o \
	-name '*.fdb_latexmk' -o \
	-name '*.synctex.gz' -o \
	-name '*.bbl' -o \
	-name '*.blg' \
	\) -print0)

exit "${Fail}"
