<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Generalized Collatz Library

## Raw map

For \(q,c,d\in\mathbb Z\) with \(|d|\ge2\), define
\[
F_{q,c,d}(n)=
\begin{cases}
n/d,&d\mid n,\\
qn+c,&d\nmid n.
\end{cases}
\]
The divisor retains its sign. Division has precedence, including at zero.
The classical raw map is \(F_{3,1,2}\).

## Foundations

[Definitions and theorems](Foundations.Main.StartHere/README.md) ·
[Detailed proofs](Foundations.Main.StartHere/tex/Foundations.tex) ·
[Formal proofs](Foundations.Main.StartHere/lean/GeneralizedCollatz.lean) ·
[Exact arithmetic](Foundations.Main.StartHere/go/Dynamics.go)

- A legal word is the unique raw itinerary of the same length.
- Chronological affine composition retains the full additive offset.
- Legal cycle closure implies \((Q-P)n=B\).
- For \(\Delta\ne0\),
  \[
  \frac{|\Delta|}{\gcd(|\Delta|,|b|)}\mid |c|
  \quad\Longleftrightarrow\quad
  \exists n\in\mathbb Z:\ \Delta n=cb.
  \]
  This scalar equation does not imply intermediate branch legality.
- Labelled graphs and marked systems form categories.
- A target-reflecting semiconjugacy transfers capture at the same time.
- A variable-clock semiconjugacy transfers forward capture at the accumulated time.

## Reductions

### Coprime scaling and offset normalization

[QCD.Scaling.001](QCD.Scaling.001/README.md) proves that coprime scaling preserves
the exact raw clock. If
\[
\gcd(|c|,|d|)=1,
\qquad c\mid q^k,
\]
then every signed integer orbit enters \(c\mathbb Z\) after at most \(k\) affine
events. From that entry onward it is exactly \(c\) times an orbit of
\(F_{q,1,d}\). This gives an all-seed capture equivalence for arbitrary targets,
with a positive-domain version when \(q\ge0\), \(c>0\), and \(d>0\).

## Other map conventions

A residue-wise affine map has the form
\[
T(n)=\frac{q_r n+c_r}{d},\qquad r=n\bmod d,
\qquad c_r\equiv-q_r r\pmod d.
\]
A common multiplier is the special case \(q_r=q\).
This is a different map from raw branching. Shortcut, odd-accelerated and
first-division maps also have their own definitions and clocks.

## Build

`make` and `make lean` build the formal library. The `tex` profile uses pdfLaTeX
and BibTeX with `amsalpha`; the `go` profile uses `CGO_ENABLED=0`.

[Homomorphism theorem examples](Templates/lean/HomomorphismTheorems.lean) ·
[TeX example](Templates/tex/Template.tex) ·
[Go example](Templates/go/HomomorphismTheorems.go)

## License

[CC-BY-4.0](LICENSE.md).
