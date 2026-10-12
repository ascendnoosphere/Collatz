<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Classical capture recovery and absorbing ternary tails

[Detailed proofs](tex/ClassicalAbsorption.tex) ·
[Formal proofs](lean/ClassicalAbsorption.lean) ·
[Exact replay](go/ClassicalAbsorption.go)

## Parameters and clocks

For independent natural exponents \(a,b\), put \(\sigma=3^b\) and define the
**raw, division-first** map
\[
F_{a,b}(n)=
\begin{cases}
n/2,&2\mid n,\\
2^a(3n+\sigma),&2\nmid n.
\end{cases}
\]
Its coefficients are \((q,c,d)=(3\cdot2^a,2^a3^b,2)\). Integer states may
have either sign. The all-seed capture assertion below quantifies over
**positive** states, as does the classical assertion. Neither exponent is
required to be positive.

Write \(G_b=F_{0,b}\) and \(H=F_{0,0}=F_{3,1,2}\), the classical raw map.
One \(G_b\) division costs one \(F_{a,b}\) raw step; one \(G_b\) affine
instruction costs \(a+1\). If \(R(k,n)\) counts affine instructions among
the first \(k\) compressed steps, then
\[
F_{a,b}^{\,k+aR(k,n)}(n)=G_b^k(n).
\]
This is variable-clock transport, not one-step conjugacy.

## Results

| Result ID | Statement |
| --- | --- |
| `QCD.ClassicalRecovery.001.CompressionCapture` | For every signed seed, reaching the exact target \(\sigma\) under \(F_{a,b}\) is equivalent to reaching it under \(G_b\). |
| `QCD.ClassicalRecovery.001.AbsorbingTail` | Every positive \(G_b\) seed enters \(\sigma\mathbb Z\) with at most \(b\) compressed affine instructions and has a common positive normalized tail. The corresponding original orbit has an exact tail on the same original raw clock. |
| `QCD.ClassicalRecovery.001.PositiveCaptureEquivalence` | For each fixed \(a,b\), all positive \(F_{a,b}\) seeds reach \(\sigma\) if and only if all positive classical raw seeds reach \(1\). |
| `QCD.ClassicalRecovery.001.PrimitiveCycle` | The designated state \(\sigma\) has primitive original raw period exactly \(a+3\). |

### Exact target reflection

The target \(\sigma\) is odd. At any strict interior of an expanded affine
block, the state has a factor of \(2\); hence it cannot equal \(\sigma\).
Positive clock coverage accounts for every original raw time, not just
compressed endpoints. Thus for every \(n\in\mathbb Z\),
\[
(\exists r\ge0:F_{a,b}^r(n)=\sigma)
\quad\Longleftrightarrow\quad
(\exists k\ge0:G_b^k(n)=\sigma).
\]

### Common absorbing tail

For every positive \(n\) there exist \(t\ge0\) and \(m>0\) such that
\[
G_b^t(n)=\sigma m,
\qquad A_{G_b}(t,n)\le b,
\qquad
G_b^{t+s}(n)=\sigma H^s(m)\quad\text{for every }s\ge0.
\]
Here \(A_{G_b}\) counts actual affine instructions in that compressed raw
prefix; it is not a bound on its number of division instructions. The proof
uses the decreasing lexicographic rank consisting of the remaining affine
budget and the current magnitude. Coprimality of \(\sigma\) and \(2\)
preserves the divisibility obligation at legal divisions.

At the expanded entry time \(r=t+aR(t,n)\), the original map has the tail
\[
F_{a,b}^{r+s}(n)=\sigma F_{a,0}^{s}(m)\quad\text{for every }s\ge0.
\]
This last identity uses the **same original raw time** \(s\). Comparing its
right-hand side with \(H\) instead requires the additional binary variable
clock. The entry witness \(m\) need not equal the original seed \(n\).
Scaling conjugates only the invariant lattice \(\sigma\mathbb Z\), not the
entire integer state space.

### Universal positive capture

The exact equivalence is
\[
\bigl(\forall n>0\ \exists r\ge0:F_{a,b}^r(n)=3^b\bigr)
\quad\Longleftrightarrow\quad
\bigl(\forall m>0\ \exists s\ge0:H^s(m)=1\bigr).
\]
The forward direction restricts to seeds \(\sigma m\) and cancels the
nonzero scale after target reflection. The reverse direction uses the
common absorbing tail. This identifies the remaining classical obligation;
it does not prove either universal capture assertion and does not compare
classical capture at the same original seed pointwise.

### Primitive original cycle

The complete legal cycle is
\[
\sigma\longmapsto2^{a+2}\sigma\longmapsto2^{a+1}\sigma
\longmapsto\cdots\longmapsto2\sigma\longmapsto\sigma.
\]
For \(0\le j\le a+2\),
\[
F_{a,b}^{j+1}(\sigma)=2^{a+2-j}\sigma.
\]
Every earlier positive time has a strictly positive binary exponent and
therefore cannot return to \(\sigma\). The period is \(a+3\), not a
compressed or shortcut period. This describes the designated cycle, not
all cycles of the family.

## Computed instances

- \((a,b)=(0,0)\): \(1,4,2,1\), primitive raw period \(3\).
- \((a,b)=(2,1)\): \(3,48,24,12,6,3\), primitive raw period \(5\).
  Seed \(1\) has prefix \(1,24,12,6\), entering \(3\mathbb Z\) at
  original time \(3\) with normalized seed \(2\). Its next state is the
  target \(3\).
- \((a,b)=(1,2)\): \(9,72,36,18,9\), primitive raw period \(4\).
  Seed \(1\) enters \(9\mathbb Z\) along
  \(1,24,12,6,3,36,18\) at original time \(6\); the compressed prefix
  uses two affine instructions. The next original state is \(9\).

## Exact finite replay

`go/ClassicalAbsorption.go` uses signed arbitrary-precision integers and
checks legal raw branches, compression endpoints, exclusion of the odd
target from strict interiors, the compressed affine entry budget, both
post-entry clock correspondences, and every designated cycle phase.
Its main box has \(0\le a\le16\), \(0\le b\le12\), and
\(1\le|n|\le64\): \(17\cdot13\cdot128=28288\) seed certificates.
These are not distinct-orbit counts or an infinite capture certificate.

The callable computational contract permits \(0\le a\le64\),
\(0\le b\le32\), and nonzero seeds of at most \(512\) bits. It refuses
invalid configurations before mutation and refuses nil, zero, oversized,
or unconfigured seed inputs. A prefix cap of \(4096\) compressed steps,
a \(32\)-step original tail, and \(16\) classical comparison steps
bound replay only; these limits do not restrict the theorems. Exceeding a
prefix cap is a computational refusal, not evidence of noncapture.

Eight chunks own disjoint workspaces and result slots. Each workspace
reserves \(2048\)-bit operands before its hot loops. The allocation tests
measure zero warmed allocations only at \((a,b)=(0,0),(16,12),(64,32),(3,0)\)
with seed \(27\); they are not a universal allocation claim. The primitive
cycle test covers all \(65\cdot33=2145\) bounded exponent presentations,
not all possible cycles. Replay is self-contained.

```sh
make lean
make go GOFILE=QCD.ClassicalRecovery.001/go/ClassicalAbsorption.go
CGO_ENABLED=0 go test -count=1 ./QCD.ClassicalRecovery.001/go
CGO_ENABLED=0 go vet ./QCD.ClassicalRecovery.001/go
make tex TEXFILE=QCD.ClassicalRecovery.001/tex/ClassicalAbsorption.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```

## Dependencies

The detailed proof uses the exact guarded scaling and offset-entry results
of [`QCD.Scaling.001`](../QCD.Scaling.001/README.md), the binary block clock
of [`QCD.TimeCompression.001`](../QCD.TimeCompression.001/README.md), and
full raw-time target recovery of
[`QCD.TimeCompression.002`](../QCD.TimeCompression.002/README.md).
Precise statements are in the adjacent TeX document and bibliography.

The broader family \((3c,c,2)\), with \(c=2^a u\) and odd \(u\), compresses
to \((3u,u,2)\) and normalizes to \((3u,1,2)\). Its multiplier is classical
\(3\) only when \(u=1\); that broader family is not identified with the
classical map by this result.
