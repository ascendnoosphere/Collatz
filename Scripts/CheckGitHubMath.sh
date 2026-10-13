#!/usr/bin/env bash
# SPDX-License-Identifier: CC-BY-4.0
# Check GitHub GFM recognition and exact TeX payloads, not live browser layout.
set -euo pipefail

# The authenticated gh CLI renders only maintained repository Markdown, never source programs.
python3 - "$@" <<'PY'
from argparse import ArgumentParser
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
from html import unescape
from html.parser import HTMLParser
from pathlib import Path
from tempfile import NamedTemporaryFile
import json
import re
import subprocess
import sys

# Backslash parity detects escaped Markdown delimiters and literal TeX percent signs.
def Escaped(source, index):
    count = 0
    while index > 0 and source[index - 1] == "\\":
        count += 1
        index -= 1
    return count % 2 == 1

# Extract source formulas while keeping ordinary code examples outside the contract.
def MathTokens(source):
    tokens = []
    index = 0
    while index < len(source):
        if index == 0 or source[index - 1] == "\n":
            end = source.find("\n", index)
            end = len(source) if end < 0 else end
            fence = re.match(r"^( {0,3})(`{3,}|~{3,})(.*)$", source[index:end])
            if fence:
                marker, info = fence[2], fence[3].strip()
                close = re.compile(r"^ {0,3}" + re.escape(marker[0]) +
                                   "{" + str(len(marker)) + r",}[ \t]*$", re.M)
                closing = close.search(source, min(end + 1, len(source)))
                if not closing:
                    raise ValueError("unclosed Markdown fence")
                if info == "math":
                    indent = fence[1]
                    raw = source[end + 1:closing.start()]
                    body = "\n".join(line[len(indent):] if line.startswith(indent) else line
                                     for line in raw.splitlines()).strip()
                    tokens.append({"tex": body, "display": True})
                index = closing.end()
                continue
        if source[index] == "$" and not Escaped(source, index):
            if source.startswith("$`", index):
                closing = source.find("`$", index + 2)
                if closing < 0:
                    raise ValueError("unclosed code-delimited math")
                body = source[index + 2:closing]
                if "\n" in body or "`" in body:
                    raise ValueError("unsupported code-delimited inline payload")
                tokens.append({"tex": body.strip(), "display": False})
                index = closing + 2
                continue
            display = source.startswith("$$", index)
            width = 2 if display else 1
            index += width
            start = index
            while index < len(source):
                if source.startswith("$" * width, index) and not Escaped(source, index):
                    break
                index += 1
            if index == len(source):
                raise ValueError("unclosed dollar math")
            body = source[start:index].strip()
            if not display:
                if "\n" in body and any(char == "%" and not Escaped(body, pos)
                                        for pos, char in enumerate(body)):
                    raise ValueError("multiline commented inline math")
                body = body.replace("\n", " ")
            tokens.append({"tex": body, "display": display})
            index += width
            continue
        if source[index] == "`" and not Escaped(source, index):
            marker = re.match(r"`+", source[index:])[0]
            close = re.compile(r"(?<!`)" + re.escape(marker) + r"(?!`)")
            closing = close.search(source, index + len(marker))
            if closing:
                index = closing.end()
                continue
            index += len(marker)
            continue
        index += 1
    return tokens

# GitHub transports inline TeX through two HTML layers, display TeX through one.
# Decode fixed layer counts, never repeatedly or until a source-dependent match appears.
class MathHTML(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.rows = []
        self.body = None
        self.display = False

    # These callback names are fixed by the standard-library HTMLParser interface.
    def handle_starttag(self, tag, attrs):
        if tag == "math-renderer":
            if self.body is not None:
                raise ValueError("nested GitHub math renderer")
            classes = dict(attrs).get("class", "").split()
            modes = {"js-inline-math", "js-display-math"} & set(classes)
            if len(modes) != 1:
                raise ValueError("unrecognized GitHub math renderer class")
            self.display = "js-display-math" in classes
            self.body = []
        elif self.body is not None:
            raise ValueError("unexpected nested element in GitHub math payload")

    # HTMLParser has already removed the surrounding DOM's entity layer here.
    def handle_data(self, data):
        if self.body is not None:
            self.body.append(data)

    # Remove only inline transport's extra layer, preserving literal TeX entity text.
    def handle_endtag(self, tag):
        if tag == "math-renderer":
            if self.body is None:
                raise ValueError("unmatched GitHub math renderer")
            value = "".join(self.body).strip()
            if not self.display:
                value = unescape(value)
            delimiter = "$$" if self.display else "$"
            if (len(value) < 2 * len(delimiter) or not value.startswith(delimiter)
                    or not value.endswith(delimiter)):
                raise ValueError("unrecognized GitHub math payload delimiters")
            body = value[len(delimiter):-len(delimiter)].strip()
            self.rows.append({"tex": body, "display": self.display})
            self.body = None

# Source/renderer cardinality, order, display mode and every TeX byte must agree.
def CheckPayload(source, rendered):
    expected = MathTokens(source)
    parser = MathHTML()
    parser.feed(rendered)
    parser.close()
    if parser.body is not None:
        raise ValueError("unclosed GitHub math renderer")
    if len(expected) != len(parser.rows):
        raise ValueError(f"math recognition count differs: source={len(expected)}, "
                         f"GitHub={len(parser.rows)}")
    for index, (left, right) in enumerate(zip(expected, parser.rows), 1):
        if left != right:
            raise ValueError(f"math payload {index} changed: source={left!r}, GitHub={right!r}")
    return expected

# Reject source aliases and hidden/instruction documents before any outbound request.
def ResolvePage(root, name):
    path = Path(name)
    path = path if path.is_absolute() else root / path
    if not path.is_relative_to(root):
        raise ValueError("Markdown path leaves the repository: " + name)
    relative = path.relative_to(root)
    if (any(part.startswith(".") for part in relative.parts)
            or path.name in {"AGENTS.md", "LICENSE.md"} or path.suffix != ".md"):
        raise ValueError("not a maintained Markdown page: " + name)
    current = root
    for part in relative.parts:
        current = current / part
        if current.is_symlink():
            raise ValueError("symlink Markdown path: " + name)
    if not path.is_file() or not path.resolve().is_relative_to(root):
        raise ValueError("not a regular repository Markdown page: " + name)
    return path

# Validate every existing output component, not merely the directory's resolved name.
def ResolveEvidence(root, name, directory=False):
    path = Path(name)
    path = path if path.is_absolute() else root / path
    if not path.is_relative_to(root / ".pi") or ".." in path.parts:
        raise ValueError("GitHub evidence output must stay inside the repository's .pi directory")
    current = root
    for part in path.relative_to(root).parts:
        current = current / part
        if current.is_symlink():
            raise ValueError("symlink GitHub evidence path: " + str(current))
        if current.exists():
            if current != path or directory:
                if not current.is_dir():
                    raise ValueError("not a GitHub evidence directory: " + str(current))
            elif not current.is_file():
                raise ValueError("not a regular GitHub evidence file: " + str(current))
    if not path.resolve().is_relative_to(root / ".pi"):
        raise ValueError("resolved GitHub evidence output leaves the repository's .pi directory")
    return path

# Recheck at writes; replace a temporary file rather than truncate a hard-linked destination.
def WriteEvidence(root, path, body):
    path = ResolveEvidence(root, path)
    path.parent.mkdir(parents=True, exist_ok=True)
    ResolveEvidence(root, path)
    temporary = None
    try:
        with NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                prefix=".GitHubMath", delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(body)
        ResolveEvidence(root, path)
        temporary.replace(path)
    finally:
        if temporary is not None:
            temporary.unlink(missing_ok=True)

# Use gh's stored authentication without printing credentials or executing document content.
def RenderPage(root, output, repo, path):
    name = path.relative_to(root).as_posix()
    cache = ResolveEvidence(root, output / (name + ".html"))
    source = path.read_text(encoding="utf-8")
    request = json.dumps({"text": source, "mode": "gfm", "context": repo})
    reply = subprocess.run(["gh", "api", "markdown", "--method", "POST", "--input", "-"],
                           input=request, capture_output=True, text=True, timeout=90)
    if reply.returncode:
        raise RuntimeError(reply.stderr.strip() or "GitHub Markdown API failed")
    WriteEvidence(root, cache, reply.stdout)
    try:
        formulas = CheckPayload(source, reply.stdout)
    except ValueError as error:
        raise ValueError(name + ": " + str(error)) from error
    if path.read_text(encoding="utf-8") != source:
        raise RuntimeError("Markdown source changed during request: " + name)
    return {"path": name, "source_sha256": sha256(source.encode()).hexdigest(),
            "math": formulas}

# Independent requests have a bounded four-worker budget and preserve sorted page order.
def Main():
    args = ArgumentParser(description="Check exact GitHub GFM math payload preservation")
    args.add_argument("--repo", default="ascendnoosphere/Collatz")
    args.add_argument("--output", default=".pi/Markdown/GitHub")
    args.add_argument("paths", nargs="*")
    options = args.parse_args()
    root = Path.cwd().resolve()
    actual = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"],
                                        text=True).strip()).resolve()
    if actual != root:
        raise ValueError("run from the repository root")
    output = ResolveEvidence(root, options.output, directory=True)
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", options.repo):
        raise ValueError("GitHub context must be owner/repository")
    listed = options.paths
    if not listed:
        listed = subprocess.check_output(["git", "ls-files", "-z", "*.md"]).decode().split("\0")
        listed = [name for name in listed if name and
                  Path(name).name not in {"AGENTS.md", "LICENSE.md"}]
    paths = sorted({ResolvePage(root, name) for name in listed})
    if not paths:
        raise ValueError("no maintained Markdown pages selected")
    evidence = ResolveEvidence(root, output / "MathPayloads.json")
    # All selected destinations must be safe before the first page is sent to GitHub.
    for path in paths:
        ResolveEvidence(root, output / (path.relative_to(root).as_posix() + ".html"))
    output.mkdir(parents=True, exist_ok=True)
    ResolveEvidence(root, output, directory=True)
    with ThreadPoolExecutor(max_workers=4) as executor:
        futures = [executor.submit(RenderPage, root, output, options.repo, path) for path in paths]
        rows = [future.result() for future in futures]
    WriteEvidence(root, evidence, json.dumps(rows, ensure_ascii=False, indent=2))
    count = sum(len(row["math"]) for row in rows)
    print(f"GitHub GFM math payload check passed: {len(rows)} pages; {count} expressions")
    print(f"Exact source/HTML math count, order, display modes and TeX payloads agree: {evidence}")
    print("Scope: not MathJax compilation, live GitHub layout, or mathematical truth")

if __name__ == "__main__":
    try:
        Main()
    except (ValueError, RuntimeError, OSError, subprocess.SubprocessError) as error:
        print("GitHub GFM math payload check failed:", error, file=sys.stderr)
        raise SystemExit(1)
PY
