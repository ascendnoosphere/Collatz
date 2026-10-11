# Generalized Collatz Library

This library stores reductions and related data for generalized Collatz maps and their
residue-class affine forms \(qx+c \bmod d\). Integers \(q,c\) and \(d\geq2\) define
the branching map below. Positive-integer dynamics additionally require positive outputs.

## Default map

\[
T_{q,c,d}(x)=
\begin{cases}
x/d & \text{if }d\mid x\\
qx+c & \text{if }d\nmid x
\end{cases}
\]

Recovers \(3x+1\) at \(d=2\), \(q=3\), \(c=1\).

## Stored variants

Single-\(q\) residue form:

\[
T(x)=\frac{qx+c_{x\bmod d}}{d},\qquad c_r\equiv -qr\pmod{d}
\]

Fully general residue form:

\[
T(x)=\frac{q_rx+c_r}{d}\quad\text{on each residue }r\bmod d,
\qquad c_r\equiv-q_rr\pmod d
\]

## Layout

PascalCase content filenames and declared functions. Keep the conventional tool filenames
and language directories listed below; Go's entry point remains `main`.

Every content folder: `DOMAIN.SUBDOMAIN.[Concept or ID]/`

Under each such folder, as needed: `lean/`, `tex/`, `go/`, `other/`.

`Foundations.*` holds definitions and foundations.

```
Foundations.Main.StartHere/             empty definitions stub
Templates/
  lean/HomomorphismTheorems.lean
  lean/HomomorphismTheorems/{Group,Ring,Module}.lean
  tex/Template.tex
  tex/Template.bib
  go/HomomorphismTheorems.go
  go/HomomorphismTheorems_test.go
  other/                               generated plots (gitignored)
Scripts/
  CheckIgnoredPdfs.sh
  CheckIgnoredTexTemps.sh
AGENTS.md
README.md
lakefile.toml
lake-manifest.json
go.mod
go.sum
lean-toolchain
Makefile
.gitignore
LICENSE.md
```

## Build

The Makefile prepends `$(HOME)/.local/go/bin` to `PATH`.
Install the toolchain named by `lean-toolchain`, the Go version in `go.mod`, and
`latexmk` with pdfLaTeX and BibTeX before running:

```sh
make lean
make tex TEXFILE=Templates/tex/Template.tex
make go GOFILE=Templates/go/HomomorphismTheorems.go
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
PATH="$HOME/.local/go/bin:$PATH" CGO_ENABLED=0 go test ./Templates/go
```

The Go profile uses `CGO_ENABLED=0` and pure-Go Gonum. Optional BLAS backends are
not implemented by these templates. The plot is a vector 6in×4in PDF in
`Templates/other/`, with Latin Modern math glyphs and 16/14/12pt title/axis/tick
sizes. Its math handler supports the three documented TeX expressions only.
The TeX profile cleans document-specific temporary files on success and failure.

## License

`CC-BY-4.0`; see `LICENSE.md`.
