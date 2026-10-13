#!/usr/bin/env bash
# SPDX-License-Identifier: CC-BY-4.0
# Exercise static Markdown acceptance and rejection in a disposable bounded fixture.
set -euo pipefail

root="$PWD"
workspace=$(mktemp -d)
trap 'rm -rf "$workspace"' EXIT
cp "$root/Scripts/CheckMarkdown.sh" "$workspace/CheckMarkdown.sh"

# Code examples remain literal; real math, duplicate headings and local anchors are checked.
printf '%s\n' \
  '# Accepted fixture' \
  '## `Named` heading' \
  '## Named heading' \
  '[first](#named-heading) [second](#named-heading-1)' \
  '[linked](Other.md#linked-heading)' \
  '$n=\lvert x\rvert$' \
  '$`\{0,1\}`$ and $`\# A`$' \
  '``$` deliberately literal math example`$``' \
  '$$' \
  '\begin{cases}x,&x=0,\\(x+1),&x\ne0.\end{cases}' \
  '$$' \
  '```math' \
  '\frac{1}{2}' \
  '```' \
  '```text' \
  '\[ $ deliberately literal example' \
  '```' > "$workspace/README.md"
printf '%s\n' '# Linked heading' > "$workspace/Other.md"
(cd "$workspace" && bash CheckMarkdown.sh)

# Every rejected fixture must fail for the intended diagnostic, not an unrelated condition.
ExpectFailure() {
  local content="$1" expected="$2"
  printf '%s\n' "$content" > "$workspace/Bad.md"
  if (cd "$workspace" && bash CheckMarkdown.sh) > "$workspace/Result.log" 2>&1; then
    printf 'unexpected acceptance: %s\n' "$expected" >&2
    exit 1
  fi
  if ! grep -F -- "$expected" "$workspace/Result.log" >/dev/null; then
    printf 'missing expected diagnostic: %s\n' "$expected" >&2
    exit 1
  fi
  rm "$workspace/Bad.md"
}

# Negative controls cover damaged delimiters, TeX grouping, tables and local assets.
ExpectFailure '\[x\]' 'legacy math delimiter'
ExpectFailure '$x' 'unclosed inline math delimiter'
ExpectFailure '$\frac{1}{2$' 'unclosed brace in math'
ExpectFailure '$\begin{cases}x\end{matrix}$' 'mismatched TeX environment'
ExpectFailure '| $|x|$ |' 'unescaped table pipe'
ExpectFailure '[missing](Absent.md)' 'missing local target'
ExpectFailure '[missing anchor](Other.md#absent)' 'missing local heading anchor'
ExpectFailure '![missing](Missing.png)' 'missing local target'
printf 'not a PNG\n' > "$workspace/Invalid.png"
ExpectFailure '![invalid](Invalid.png)' 'invalid PNG preview'
ExpectFailure $'```math\n\\frac{1}{2\n```' 'unclosed brace in math'
ExpectFailure '$`\frac{1}{2`$' 'unclosed brace in math'
ExpectFailure '$`\[x\]`$' 'legacy math delimiter'
ExpectFailure '$`\xmapsto{x}`$' 'unsupported arrow macro'
ExpectFailure '| $`|x|`$ |' 'unescaped table pipe'
ExpectFailure $'```math\nx\n```text' 'unclosed Markdown code fence'
printf 'Markdown checker regression tests passed: accepted fixture and fifteen negative controls\n'
