#!/usr/bin/env bash
# SPDX-License-Identifier: CC-BY-4.0
# Exercise payload equality offline; these fixtures do not contact GitHub or compile TeX.
set -euo pipefail

# Load only the owned checker definitions, not its network entrypoint or document content.
python3 - "$PWD/Scripts/CheckGitHubMath.sh" <<'PY'
from contextlib import redirect_stdout
from html import escape
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from types import SimpleNamespace
from unittest.mock import patch
import json
import os
import sys

source = Path(sys.argv[1]).read_text(encoding="utf-8")
body = source.split("<<'PY'\n", 1)[1].rsplit("\nPY\n", 1)[0]
namespace = {"__name__": "PayloadRegression"}
exec(compile(body, sys.argv[1], "exec"), namespace)
check = namespace["CheckPayload"]

# Match the observed API protocol: two inline entity layers, one display layer.
def Renderer(tex, display=False, layers=None):
    delimiter = "$$" if display else "$"
    kind = "js-display-math" if display else "js-inline-math"
    encoded = delimiter + tex + delimiter
    for _ in range((1 if display else 2) if layers is None else layers):
        encoded = escape(encoded)
    return '<math-renderer class="' + kind + '">' + encoded + '</math-renderer>'

# Acceptance fixtures include escaped punctuation, entity literals and nested-list indentation.
accepted = [
    (r'$`\{0,1\}`$ and $`\# A`$ and $`\gcd(c,\,D)`$',
     Renderer(r'\{0,1\}') + Renderer(r'\# A') + Renderer(r'\gcd(c,\,D)')),
    (r'$`\text{\&amp;}`$', Renderer(r'\text{\&amp;}')),
    (r'$`\text{\&#65;}`$', Renderer(r'\text{\&#65;}')),
    (r'$`a<b \quad c>d \quad a&b`$', Renderer(r'a<b \quad c>d \quad a&b')),
    ('```math\n' + r'\text{\&amp;}' + '\n```', Renderer(r'\text{\&amp;}', True)),
    ('```math\n' + r'\text{\&#65;}' + '\n```', Renderer(r'\text{\&#65;}', True)),
    ('$$\na<b\n$$', Renderer('a<b', True)),
    ('$a<b$', Renderer('a<b')),
    (r'$a\%' + '\n+b$', Renderer(r'a\% +b')),
    ('```math\n' + r'\begin{cases}a&b,\\ c&d.\end{cases}' + '\n```',
     Renderer(r'\begin{cases}a&b,\\ c&d.\end{cases}', True)),
    ('```math\n' + r'\begin{cases}n/D,&D\mid n,\\qn+c,&D\nmid n.\end{cases}' + '\n```',
     Renderer(r'\begin{cases}n/D,&D\mid n,\\qn+c,&D\nmid n.\end{cases}', True)),
    ('  ```math\n  \\frac{1}{2}\n    \\quad x\n  ```',
     Renderer('\\frac{1}{2}\n  \\quad x', True)),
    ('```text\n\\[ $ deliberately literal\n```\n``$`literal`$``\n$`x`$', Renderer('x')),
]
for original, rendered in accepted:
    check(original, rendered)

# These controls would pass a mere recognized-expression count or a permissive TeX compiler.
rejected = [
    (r'$\{0,1\}$', Renderer('{0,1}')),
    ('$$\n' + r'\begin{cases}n/D,&D\mid n,\\qn+c,&D\nmid n.\end{cases}' + '\n$$',
     Renderer(r'\begin{cases}n/D,&D\mid n,\qn+c,&D\nmid n.\end{cases}', True)),
    ('$`x`$', ''),
    ('$`x`$ $`y`$', Renderer('y') + Renderer('x')),
    ('```math\nx\n```', Renderer('x')),
    ('$`x`$', '<math-renderer class="js-inline-math">$x$'),
    ('```math\nx', ''),
    ('$`x`$', '<math-renderer class="js-inline-math">$<span>x</span>$</math-renderer>'),
    ('$`x\ny`$', Renderer('x y')),
    ('$``x``$', Renderer('x')),
    (r'$a\\%' + '\n+b$', Renderer(r'a\\% +b')),
    (r'$`\text{\&amp;}`$', Renderer(r'\text{\&amp;}', layers=1)),
    (r'$`\text{\&amp;}`$', Renderer(r'\text{\&}')),
    ('```math\n' + r'\text{\&amp;}' + '\n```', Renderer(r'\text{\&amp;}', True, 2)),
    ('```math\n' + r'\text{\&amp;}' + '\n```', Renderer(r'\text{\&}', True)),
    ('$`x`$', '<math-renderer class="js-inline-math js-display-math">$x$</math-renderer>'),
    ('```math\n' + r'\begin{cases}a&b,\\' + '\nc&d.\\end{cases}\n```',
     Renderer(r'\begin{cases}a&b,' + chr(92) * 3 + '\nc&d.\\end{cases}', True)),
    ('  ```math\n  x+y\n  ```', '<pre lang="math"><code>x+y</code></pre>'),
]
for original, rendered in rejected:
    try:
        check(original, rendered)
    except ValueError:
        continue
    raise SystemExit('unexpected payload acceptance: ' + repr(original))
# Install one alias without touching any real repository or external file.
def InstallEvidenceAlias(kind, output, sentinel):
    if kind == 'manifest':
        (output / 'MathPayloads.json').symlink_to(sentinel)
    elif kind == 'cache-file':
        (output / 'Family').mkdir(exist_ok=True)
        (output / 'Family' / 'README.md.html').symlink_to(sentinel)
    elif kind == 'cache-directory':
        (output / 'Family').symlink_to(sentinel.parent, target_is_directory=True)
    elif kind == 'output-directory':
        external = output.parent.parent / 'ExternalOutput'
        output.rename(external)
        output.symlink_to(external, target_is_directory=True)
    elif kind == 'pi-directory':
        external = output.parent.parent / 'ExternalPi'
        output.parent.rename(external)
        output.parent.symlink_to(external, target_is_directory=True)
    elif kind == 'hardlink-manifest':
        os.link(sentinel, output / 'MathPayloads.json')
    elif kind == 'hardlink-cache':
        (output / 'Family').mkdir()
        os.link(sentinel, output / 'Family' / 'README.md.html')
    else:
        raise AssertionError('unknown evidence fixture: ' + kind)

# A fake repository and mocked API isolate containment failures from all real source files.
def EvidenceFixture(kind):
    with TemporaryDirectory(prefix='GitHubMathEvidence') as temporary:
        root = Path(temporary)
        output = root / '.pi' / 'Evidence'
        output.mkdir(parents=True)
        page = root / 'Family' / 'README.md'
        page.parent.mkdir()
        page.write_text('$`x`$\n', encoding='utf-8')
        external = root / 'External'
        external.mkdir()
        sentinel = external / 'README.md.html'
        sentinel.write_text('external sentinel\n', encoding='utf-8')
        if kind and not kind.startswith('late-'):
            InstallEvidenceAlias(kind, output, sentinel)
        before = sentinel.read_bytes()
        argv = ['CheckGitHubMath', '--output', str(output), 'Family/README.md']
        response = SimpleNamespace(returncode=0, stdout=Renderer('x'), stderr='')

        # These aliases appear after preflight and must be rejected at the actual writes.
        def MockRequest(*arguments, **keywords):
            if kind and kind.startswith('late-'):
                InstallEvidenceAlias(kind[len('late-'):], output, sentinel)
            return response

        blocked = False
        with patch.object(Path, 'cwd', return_value=root), \
                patch.object(sys, 'argv', argv), \
                patch.object(namespace['subprocess'], 'check_output', return_value=str(root)+'\n'), \
                patch.object(namespace['subprocess'], 'run', side_effect=MockRequest) as request, \
                redirect_stdout(StringIO()):
            try:
                namespace['Main']()
            except ValueError as error:
                blocked = 'symlink GitHub evidence path:' in str(error)
        if kind is None or kind.startswith('hardlink-'):
            rows = json.loads((output / 'MathPayloads.json').read_text())
            assert rows[0]['math'] == [{'tex': 'x', 'display': False}]
            assert (output / 'Family' / 'README.md.html').read_text() == Renderer('x')
        assert page.read_text() == '$`x`$\n'
        assert not list(output.rglob('.GitHubMath*'))
        return blocked, request.call_count, sentinel.read_bytes() == before

# Existing aliases block all requests; later aliases cannot redirect either kind of write.
evidence_negative = ['manifest', 'cache-file', 'cache-directory',
                     'output-directory', 'pi-directory']
late_negative = ['late-manifest', 'late-cache-file', 'late-cache-directory']
evidence_accepted = [None, 'hardlink-manifest', 'hardlink-cache']
failures = []
for kind in evidence_negative + late_negative:
    blocked, requests, intact = EvidenceFixture(kind)
    expected_requests = 1 if kind in late_negative else 0
    if not blocked or requests != expected_requests or not intact:
        failures.append(f'{kind}: blocked={blocked}, requests={requests}, sentinel_intact={intact}')
if failures:
    raise SystemExit('unexpected evidence acceptance: ' + '; '.join(failures))
for kind in evidence_accepted:
    assert EvidenceFixture(kind) == (False, 1, True)
print(f'GitHub math payload regression tests passed: {len(accepted)} accepted fixtures; '
      f'{len(rejected)} payload negative controls; '
      f'{len(evidence_accepted)} accepted evidence fixtures, '
      f'{len(evidence_negative)} pre-request and {len(late_negative)} write-time negative controls; '
      'mocked API only; no network or MathJax used')
PY
