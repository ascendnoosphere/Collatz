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
  '[full][New label] [New label][] [New label]' \
  '[new label]: Other.md#linked-heading' \
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
  if [[ -d "$workspace/.git" ]]; then
    git -C "$workspace" add Bad.md
  fi
  if (cd "$workspace" && bash CheckMarkdown.sh) > "$workspace/Result.log" 2>&1; then
    printf 'unexpected acceptance: %s\n' "$expected" >&2
    exit 1
  fi
  if ! grep -F -- "$expected" "$workspace/Result.log" >/dev/null; then
    printf 'missing expected diagnostic: %s\n' "$expected" >&2
    exit 1
  fi
  if [[ -d "$workspace/.git" ]]; then
    git -C "$workspace" rm --cached --quiet Bad.md
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
ExpectFailure $'[missing][source]\n[source]: Absent.md' 'missing local target'
ExpectFailure $'[missing][]\n[missing]: Other.md#absent' 'missing local heading anchor'
ExpectFailure $'![missing][picture]\n[picture]: Missing.png' 'missing local target'
ExpectFailure '[literal][undefined]' 'undefined reference label'
# Fresh-clone checks must reject local files that happen to exist but are not published.
git -C "$workspace" init --quiet
printf '%s\n' 'Ignored.md' > "$workspace/.gitignore"
git -C "$workspace" add README.md Other.md CheckMarkdown.sh .gitignore
printf '%s\n' '# Untracked local target' > "$workspace/Untracked.md"
printf '%s\n' '# Ignored local target' > "$workspace/Ignored.md"
ExpectFailure '[unpublished](Untracked.md)' 'local target is not tracked'
ExpectFailure '[ignored](Ignored.md)' 'local target is not tracked'
printf 'Markdown checker regression tests passed: accepted fixture and twenty-one negative controls\n'
