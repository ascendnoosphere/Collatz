#!/usr/bin/env bash
# CheckIgnoredPdfs.sh
# Recurse the repository. Every *.pdf must be gitignored.
# Exit 1 if any PDF is not ignored.

set -euo pipefail

Root="$(git rev-parse --show-toplevel)"
cd "${Root}"

Fail=0
while IFS= read -r -d '' Pdf; do
	if ! git check-ignore -q "${Pdf}"; then
		printf 'not ignored: %s\n' "${Pdf}"
		Fail=1
	fi
done < <(find . -path './.git' -prune -o -type f -name '*.pdf' -print0)

exit "${Fail}"
