#!/usr/bin/env bash
# SPDX-License-Identifier: CC-BY-4.0
# Check that all tracked Lean modules coexist, not just that each builds alone.
set -euo pipefail

Root="$(git rev-parse --show-toplevel)"
cd "${Root}"
Temp="$(mktemp -d "${TMPDIR:-/tmp}/CollatzImports.XXXXXX")"
trap 'rm -rf -- "${Temp}"' EXIT

# Import names are paths relative to each content folder's registered lean directory.
while IFS= read -r -d '' Source; do
    Module="${Source#*/lean/}"
    Module="${Module%.lean}"
    printf 'import %s\n' "${Module//\//.}"
done < <(git ls-files -z -- '*.lean') > "${Temp}/Imports.lean"

lake env lean "${Temp}/Imports.lean"
printf 'Lean joint-import check passed\n'
