<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Exact common-base gcd rebasing

**QCD.CommonBase.002** removes the coprime-exponent hypothesis from the
positive-divisor super-offset family. The raw map is
```math
F(n)=\begin{cases}n/D,&D\mid n,\\Qn+C,&D\nmid n,\end{cases}
\qquad Q=t^u,\quad D=t^v,\quad C=t^a s,
```
where $`t\ge2`$, $`0<u<v`$, $`a\ge u+v`$, and $`s\in\mathbb Z\setminus\{0\}`$.
Division has priority, including at zero. The base may be composite, and no
unit or indivisibility condition is imposed on $`s`$.

[Detailed proofs](tex/CommonBaseRebasing.tex) ·
[Formal proofs](lean/CommonBaseRebasing.lean) ·
[Exact raw replay](go/CommonBaseRebasing.go)

## QCD.CommonBase.002.1 — identical coefficients

Set
```math
g=\gcd(u,v),\quad T=t^g,\quad U=u/g,\quad V=v/g,
\quad A=a/g,\quad S=t^{a\bmod g}s.
```
Then $`T\ge2`$, $`0<U<V`$, $`\gcd(U,V)=1`$, $`A\ge U+V`$, and $`S\ne0`$.
Moreover
```math
Q=T^U,\qquad D=T^V,\qquad C=T^A S.
```
This changes the presentation, not the integer state, raw function, branch
guards, or time. Also $`T\le Q`$ and $`|S|\le|C|`$. If $`g>1`$, then
$`V<v`$. These identities allow direct application of
[the coprime phase theorem](../QCD.CommonBase.001/README.md).

## QCD.CommonBase.002.2 — all rebased phase rays

For a nonzero division-free state $`x=T^k w`$, with $`k<V`$ and $`T\nmid w`$,
put
```math
P=U+V,\qquad G_V(T)=\sum_{i=0}^{V-1}T^i,
\qquad \beta_k=S T^{A-U-V+1+k}G_V(T).
```
For every $`j\ge0`$,
```math
F^{jP}(x)=x+j\beta_k,
```
and the whole-base $`T`$ order remains $`k`$. Each sweep consists of $`V`$
affine edges and $`U`$ division edges. The physical raw clock is
$`P=(u+v)/g`$, not $`u+v`$ when $`g>1`$. Every rebased phase is included.
The residual $`w`$ need not be a unit modulo $`T`$.

## QCD.CommonBase.002.3 — full raw escape and sign

For every signed seed $`n\ne0`$, every integer $`M\ge0`$, and every raw time
$`r\ge0`$,
```math
|n|+(|n|+1+M D^U)P\le r\quad\Longrightarrow\quad M<|F^r(n)|.
```
Consequently $`|F^r(n)|\to\infty`$ along the full raw sequence. Also
```math
|n|+(|n|+1)P\le r\quad\Longrightarrow\quad sF^r(n)>0.
```
The latter is eventual agreement with the offset's sign. Initial divisions
and every raw intermediate step are included; the magnitude estimate is not
applied across an opposite-sign initial segment.

## QCD.CommonBase.002.4 — periodicity

Zero is fixed and is the only periodic integer point. All signed nonzero
seeds are covered by the preceding full-time escape statement.

## Examples and scope

The presentation $`(t,u,v,a,s)=(2,2,4,7,1)`$ has
$`(T,U,V,A,S)=(4,1,2,3,2)`$ and $`(Q,C,D)=(4,128,16)`$. Its raw orbits include
```math
1\longmapsto132\longmapsto656\longmapsto41,
\qquad
4\longmapsto144\longmapsto9\longmapsto164.
```
These have increments forty and one hundred sixty, respectively, with raw
clock three. The carried residual $`S=2`$ is not a unit modulo $`T=4`$.

The statements concern positive $`D`$, pure common-base $`Q`$, $`0<u<v`$, and
$`a\ge u+v`$. They do not assert a negative-divisor transfer or a conclusion
for other offset regimes or nontrivial residual multipliers in
$`Q=p^u r`$. The signed canonical prime-source family intersects this result
at $`\varepsilon=1`$, $`r=1`$, $`0<u<v`$; its broader classification is a
separate statement. Citations and complete arithmetic proofs are in the
adjacent TeX document.

## Implementations

The Lean file contains ten supporting and conclusion theorems: admissibility,
coefficient reconstruction, carried-residual nonvanishing, exact rays,
quantitative escape, full-sequence escape, eventual sign, periodicity,
phase decrease, and parameter bounds. They use the public coprime phase proof
without an additional orbit assumption.

The Go checker independently constructs the original and rebased coefficients,
replays two complete legal raw sweeps, checks all phases and branch counts,
and checks the intermediate magnitude inequality only after sign alignment.
Its finite sample has **807744 certificates**, not distinct maps or orbits.
It uses original bases two through nine, $`v\le8`$, all noncoprime
$`0<u<v`$, three offset exponents, sixteen signed residuals, 256 ordinary
signed seeds, and additional forced-phase controls. All nonzero residuals
from minus eight through eight are included, even when divisible by the base.

`Configure` rejects parameters outside $`2\le t\le9`$, $`0<u<v\le8`$,
$`u+v\le a\le256`$, and $`0<|s|\le8`$. It also accepts coprime inputs;
the finite main sample focuses on noncoprime presentations. `CheckSeed`
rejects nil, unconfigured, zero, and greater-than-512-bit seeds. These are
computational restrictions, not theorem hypotheses. Cached powers, reserved
storage, and disjoint multiplication buffers give zero warmed replay
allocations on four measured configurations; arbitrary-size performance is
not asserted. Six tests cover the named ray, large signed initial divisions,
refusals, allocation controls, and the complete finite certificate count.
Finite replay does not replace the universal proof.

```sh
make lean
CGO_ENABLED=0 go test -count=1 ./QCD.CommonBase.002/go
CGO_ENABLED=0 go vet ./QCD.CommonBase.002/go
make go GOFILE=QCD.CommonBase.002/go/CommonBaseRebasing.go
make tex TEXFILE=QCD.CommonBase.002/tex/CommonBaseRebasing.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
