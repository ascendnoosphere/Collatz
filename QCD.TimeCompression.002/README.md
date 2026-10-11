<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Full-orbit recovery and primitive cycles

[Detailed proofs](tex/CompressionRecovery.tex) ·
[Orbit recovery](lean/CompressionOutcomes.lean) ·
[Primitive periods](lean/CompressionPeriods.lean) ·
[Cycle classes](lean/CompressionCycleClasses.lean) ·
[Exact finite certificates](go/CompressionPeriods.go) ·
[Certificate tests](go/CompressionPeriods_test.go)

Let \(d,q,c\in\mathbb Z\), \(|d|\ge2\), and \(a\in\mathbb N\). Write
\[
F=F_{d^a q,d^a c,d},\qquad G=F_{q,c,d},
\]
where division precedes the affine branch, including at zero. The divisor keeps
its sign. No positivity or coprimality assumption is imposed.

For the block clock from [QCD.TimeCompression.001](../QCD.TimeCompression.001/README.md),
\[
\tau(x)=\begin{cases}1,&d\mid x,\\a+1,&d\nmid x,\end{cases}
\qquad T(k,n)=k+aR(k,n),
\]
where \(R\) counts compressed affine instructions, one has \(G^k(n)=F^{T(k,n)}(n)\).

## QCD.TimeCompression.002.1 — full raw-time recovery and orbit outcomes

For every \(r\in\mathbb N\) there exist \(k,s\in\mathbb N\) such that
\[
k\le r,\qquad 0\le s<\tau(G^k(n)),\qquad r=T(k,n)+s.
\]
The times \(T(k,n)\) are strictly increasing and satisfy
\(k\le T(k,n)\le(a+1)k\). If \(d\nmid x\) and \(1\le s\le a+1\), then
\[
F^s(x)=d^{a+1-s}G(x).
\]
For every block interior \(0\le s<\tau(x)\),
\[
\min(|x|,|G(x)|)\le |F^s(x)|
\le |d|^a\max(|x|,|G(x)|).
\]
These estimates recover the full raw orbit, rather than only a sampled subsequence.

### Same-seed orbit outcomes

For each signed integer seed \(n\), the following properties are equivalent
between \(F\) and \(G\): magnitude boundedness, full-sequence magnitude escape,
and eventual periodicity. In particular, escape means
\[
\forall M\in\mathbb N\ \exists R\in\mathbb N\ \forall r\ge R:
|F^r(n)|>M,
\]
not merely an unbounded subsequence. On the integer state space, a deterministic
orbit is magnitude bounded exactly when it is eventually periodic.

## QCD.TimeCompression.002.2 — target capture

For \(S\subseteq\mathbb Z\), same-seed capture is equivalent if
\[
x\in S,\ d\mid x\quad\Longrightarrow\quad x/d\in S.
\]
This division-closure condition is sufficient, not asserted necessary. Forward
capture transport needs no condition on \(S\). An arbitrary converse fails:
\(F_{4,4,2}(1)=8\), whereas the \(F_{1,1,2}\) orbit of \(1\) visits only \(1,2\).
For \(d=2,q=3,c=1\), capture of the exact target \(1\), and separately of
\(\{1,2\}\), is equivalent for every seed and every \(a\). This is a reduction
of those capture questions, not a proof of classical convergence.

## QCD.TimeCompression.002.3 — primitive periods

If \(n\) has primitive compressed period \(h\), its primitive raw period is
\[
P=h+aR(h,n).
\]
Conversely, primitiveness at this expanded time implies primitiveness at
compressed time \(h\). The proof excludes returns inside the skipped division
runs, not merely at shorter sampled times.

## QCD.TimeCompression.002.4 — recovery of a raw cycle

Every nonzero primitive raw cycle has an affine phase \(x\) with a primitive
compressed period \(h\), and its primitive raw period is the same displayed
formula evaluated at \(x\). Zero has primitive period one in both maps.
Raw periodicity at an arbitrary seed does not imply compressed periodicity at
that same seed: \(8\) is periodic for \(F_{4,4,2}\), but its \(F_{1,1,2}\) orbit
has a transient before entering \(1\leftrightarrow2\).

## QCD.TimeCompression.002.5 — a bijection of cycle classes

Restrict to periodic points, and identify two points precisely when each is a
forward iterate of the other. Expansion induces a bijection from the resulting
cycle classes of \(G\) to those of \(F\), including the zero class.
Injectivity uses exclusion of **every** periodic compressed point from every
positive-time block interior. Surjectivity chooses an affine phase of a nonzero
raw cycle, or zero. Neither a one-step conjugacy nor a bijection of the periodic
point sets themselves is asserted.

## Reduction and finite computation

The original and replacement obligations use the same signed seeds. For
boundedness, escape and eventual periodicity, recovery is bidirectional; for
capture it is bidirectional under the stated target condition. Primitive cycles
recover after the specified phase selection. The coefficient height satisfies
\[
\max(|d^a q|,|d^a c|)=|d|^a\max(|q|,|c|).
\]
It strictly decreases when \(a>0\) and \((q,c)\ne(0,0)\). The identity case
\(a=0\) and the zero coefficient pair supply transport without strict decrease.
No generic solution of the replacement capture problem is assumed.

The Go program searches compressed trajectories for at most 32 steps, then
checks an encountered primitive cycle by replaying **every** raw instruction up
to its expanded period and rejecting each shorter positive return. Its grid is
\[
d\in\{-5,-4,-3,-2,2,3,4,5\},\quad 0\le a\le3,\quad
-3\le q,c\le3,\quad -30\le n\le30.
\]
It contains 95,648 seed-parameter cases. The reference run produces 58,864
cycle-expansion certificates; these are not distinct cycle classes. Cases with
no repeat within 32 steps remain undecided. Signed division, zero, interior raw
phases and resource-contract refusal have separate tests. The finite replay is
not the proof of the universal theorems above.

```sh
make lean
CGO_ENABLED=0 go test ./QCD.TimeCompression.002/go
CGO_ENABLED=0 go vet ./QCD.TimeCompression.002/go
make go GOFILE=QCD.TimeCompression.002/go/CompressionPeriods.go
make tex TEXFILE=QCD.TimeCompression.002/tex/CompressionRecovery.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
