#!/usr/bin/env bash
# SPDX-License-Identifier: CC-BY-4.0
# Check maintained Markdown syntax and local assets; this is not a browser-rendering test.
set -euo pipefail

# Run from the repository root so ignored build artifacts cannot mask broken tracked links.
python3 - <<'PY'
from pathlib import Path
from urllib.parse import unquote, urlsplit
import re
import struct
import subprocess
import sys
import unicodedata

root = Path.cwd()
errors = []
files = []

# In a repository, the index defines maintained pages and assets available in a fresh clone.
def TrackedPaths():
    if not (root / ".git").exists():
        return None
    result = subprocess.run(["git", "ls-files", "--cached", "-z"], cwd=root,
                            check=True, stdout=subprocess.PIPE)
    return {Path(name.decode("utf-8")) for name in result.stdout.split(b"\0") if name}

tracked = TrackedPaths()

# Report exact source locations so a syntax failure can be repaired without guessing.
def Report(path, line, message):
    errors.append(f"{path.relative_to(root)}:{line}: {message}")

# An odd run of backslashes escapes the following Markdown punctuation.
def Escaped(text, index):
    count = 0
    while index > 0 and text[index - 1] == "\\":
        count += 1
        index -= 1
    return count % 2 == 1

# Protected math keeps its TeX payload; ordinary inline code remains a literal example.
def WithoutCode(line):
    output = []
    index = 0
    while index < len(line):
        if line.startswith("$`", index) and not Escaped(line, index):
            closing = line.find("`$", index + 2)
            if closing >= 0:
                output.append("$" + line[index + 2:closing] + "$")
                index = closing + 2
                continue
        if line[index] == "`" and not Escaped(line, index):
            marker = re.match(r"`+", line[index:])[0]
            closing = re.search(r"(?<!`)" + re.escape(marker) + r"(?!`)",
                                line[index + len(marker):])
            if closing:
                index += len(marker) + closing.end()
                continue
        output.append(line[index])
        index += 1
    return "".join(output)

# Retain math fences but ignore executable examples and their literal syntax.
def Visible(path, strip_code=True):
    lines = path.read_text(encoding="utf-8").splitlines()
    fence = None
    opening = 0
    visible = []
    math_fence = False
    for number, line in enumerate(lines, 1):
        match = re.match(r"^\s*(`{3,}|~{3,})(.*)$", line)
        if fence is not None:
            if (match and match[1][0] == fence[0] and len(match[1]) >= fence[1]
                    and not match[2].strip()):
                if math_fence:
                    visible.append((number, "$$"))
                fence = None
            elif math_fence:
                visible.append((number, line))
            continue
        if match:
            fence = (match[1][0], len(match[1]))
            math_fence = match[2].strip() == "math"
            if math_fence:
                visible.append((number, "$$"))
            opening = number
            continue
        visible.append((number, WithoutCode(line) if strip_code else line))
    if fence is not None:
        Report(path, opening, "unclosed Markdown code fence")
    return visible

# Balanced TeX grouping and environments detect damaged formulas, not their truth.
def CheckTex(path, opening, body):
    braces = []
    for index, character in enumerate(body):
        if Escaped(body, index):
            continue
        if character == "{":
            braces.append(index)
        elif character == "}":
            if not braces:
                Report(path, opening, "unmatched closing brace in math")
                return
            braces.pop()
    if braces:
        Report(path, opening, "unclosed brace in math")
    environments = []
    for match in re.finditer(r"\\(begin|end)\{([^}]+)\}", body):
        if match[1] == "begin":
            environments.append(match[2])
        elif not environments or environments.pop() != match[2]:
            Report(path, opening, "mismatched TeX environment in math")
            return
    if environments:
        Report(path, opening, "unclosed TeX environment in math")

# Check supported delimiters and reject table-cell pipes within mathematical spans.
def CheckMath(path, visible):
    state = None
    opening = 0
    body = []
    for number, line in visible:
        for match in re.finditer(r"\\[()\[\]]", line):
            if not Escaped(line, match.start()):
                Report(path, number, "legacy math delimiter; use $ or $$ outside code")
        if "\\xmapsto" in line:
            Report(path, number, "unsupported arrow macro; use \\xrightarrow")
        table = line.lstrip().startswith("|")
        index = 0
        while index < len(line):
            if line[index] != "$" or Escaped(line, index):
                if state is not None:
                    body.append(line[index])
                if table and state == "inline" and line[index] == "|" and not Escaped(line, index):
                    Report(path, number, "unescaped table pipe in math; use \\lvert or \\mid")
                index += 1
                continue
            token = "display" if line[index:index + 2] == "$$" else "inline"
            if state is None:
                state, opening = token, number
                body = []
            elif token == state:
                CheckTex(path, opening, "".join(body))
                state = None
            else:
                Report(path, number, "mixed inline/display dollar delimiters")
            index += 2 if token == "display" else 1
        if state is not None:
            body.append("\n")
        if table and state == "inline":
            Report(path, number, "inline math crosses a table-row boundary")
    if state is not None:
        Report(path, opening, f"unclosed {state} math delimiter")

# Static ATX headings and explicit HTML ids cover the anchors used by this library.
def HeadingAnchors(path):
    anchors = set()
    counts = {}
    source = path.read_text(encoding="utf-8")
    for number, line in Visible(path, strip_code=False):
        match = re.match(r"^\s{0,3}#{1,6}\s+(.+?)\s*#*\s*$", line)
        if not match:
            continue
        heading = re.sub(r"<[^>]*>", "", match[1]).lower()
        heading = re.sub(r"!?\[([^\]]+)\]\([^)]+\)", r"\1", heading)
        slug = "".join(character for character in heading
                       if character.isalnum() or character in "-_ "
                       or unicodedata.category(character).startswith("M"))
        slug = slug.replace(" ", "-")
        count = counts.get(slug, 0)
        counts[slug] = count + 1
        anchors.add(slug if count == 0 else f"{slug}-{count}")
    anchors.update(re.findall(r'<[^>]+\b(?:id|name)=["\']([^"\']+)["\']', source))
    return anchors

# Label folding covers ordinary single-line reference links, not arbitrary CommonMark syntax.
def ReferenceLabel(label):
    return re.sub(r"\s+", " ", label.strip()).casefold()

# The same local-asset contract applies to inline and reference-style links.
def CheckTarget(path, number, target, is_image):
    target = target.strip("<>")
    parsed = urlsplit(target)
    if parsed.scheme or parsed.netloc:
        return
    asset = ((path.parent / unquote(parsed.path)) if parsed.path else path).resolve()
    if not asset.is_relative_to(root):
        Report(path, number, f"local link leaves the repository: {target}")
        return
    if not asset.exists():
        Report(path, number, f"missing local target: {target}")
        return
    relative = asset.relative_to(root)
    if tracked is not None:
        published = relative in tracked
        if asset.is_dir():
            published = any(relative in name.parents for name in tracked)
        if not published:
            Report(path, number, f"local target is not tracked: {target}")
    if asset.suffix.lower() == ".md" and parsed.fragment:
        if unquote(parsed.fragment) not in HeadingAnchors(asset):
            Report(path, number, f"missing local heading anchor: {target}")
    if is_image and asset.suffix.lower() == ".pdf":
        Report(path, number, "PDF image embed is not a GitHub preview; use PNG")
    if is_image and asset.suffix.lower() == ".png":
        with asset.open("rb") as stream:
            header = stream.read(24)
        if len(header) != 24 or header[:8] != b"\x89PNG\r\n\x1a\n":
            Report(path, number, f"invalid PNG preview: {target}")
        else:
            width, height = struct.unpack(">II", header[16:24])
            if width == 0 or height == 0:
                Report(path, number, f"empty PNG preview: {target}")

# Local inline, full, collapsed and defined shortcut references are checked without a renderer.
def CheckLinks(path, visible):
    definitions = {}
    definition_lines = set()
    for number, line in visible:
        match = re.match(r"^ {0,3}\[([^\]]+)\]:\s*(<[^>]+>|\S+)", line)
        if match and not match[1].startswith("^"):
            definitions.setdefault(ReferenceLabel(match[1]), match[2])
            definition_lines.add(number)
            CheckTarget(path, number, match[2], False)
    for number, line in visible:
        if number in definition_lines:
            continue
        for match in re.finditer(r"(!?)\[[^\]]*\]\(([^\s)]+)(?:\s+\"[^\"]*\")?\)", line):
            if not Escaped(line, match.start()):
                CheckTarget(path, number, match[2], bool(match[1]))
        for match in re.finditer(r"(!?)\[([^\]]+)\](?:\[([^\]]*)\])?", line):
            if Escaped(line, match.start()) or line[match.end():].startswith("("):
                continue
            label = ReferenceLabel(match[3] or match[2])
            if label in definitions:
                CheckTarget(path, number, definitions[label], bool(match[1]))
            elif match[3] is not None and not label.startswith("^"):
                Report(path, number, f"undefined reference label: {label}")

# Hidden caches and instruction documents are not maintained mathematical pages.
for path in sorted(root.rglob("*.md")):
    relative = path.relative_to(root)
    if any(part.startswith(".") for part in relative.parts):
        continue
    if path.name in {"AGENTS.md", "LICENSE.md"}:
        continue
    if tracked is not None and relative not in tracked:
        continue
    files.append(path)
    visible = Visible(path)
    CheckMath(path, visible)
    CheckLinks(path, visible)

for error in errors:
    print(error)
if errors:
    print(f"Markdown static check failed: {len(errors)} findings in {len(files)} pages")
    sys.exit(1)
print(f"Markdown static checks passed: {len(files)} pages; math, local links, headings and PNGs")
print("Scope: tracked pages/assets when in Git; all pages in standalone fixtures")
print("Lexical checks only; no MathJax evaluation, external-link or live GitHub-render verification")
PY
