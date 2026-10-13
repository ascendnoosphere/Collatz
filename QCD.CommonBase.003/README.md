<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# High-offset raw escape for arbitrary positive common-base exponents

**QCD.CommonBase.003** removes the multiplier-exponent ordering restriction.
The signed raw map has division priority:
```math
F(n)=\begin{cases}n/D,&D\mid n,\\Qn+C,&D\nmid n,\end{cases}
\qquad Q=t^u,\quad D=t^v,\quad C=t^a s,
```
where $`t\ge2`$, $`u,v>0`$, $`a\ge u+v`$, and $`s\ne0`$ is an integer.
Every nonzero signed seed escapes in magnitude along the full raw sequence
and ultimately has the offset's sign. Zero is fixed and is the only periodic
integer point. The base may be composite; exponent coprimality and unit or
indivisibility conditions on the residuals are not required.

[Detailed proofs](tex/CommonBaseGeneralHighOffset.tex) ·
[Formal outcomes](lean/CommonBaseGeneralHighOffset.lean) ·
[Formal physical rays](lean/CommonBaseGeneralHighOffsetRay.lean) ·
[Signed additive child](lean/AdditiveDivisibleOffset.lean) ·
[Exact replay](go/CommonBaseGeneralHighOffset.go)

## QCD.CommonBase.003.1 — exponent compression and recovery

Write
```math
m=\lfloor u/v\rfloor,\qquad b=u\bmod v,\qquad A=a-vm.
```
Then $`0\le b<v`$, $`A\ge b+v`$, and the coefficients satisfy
```math
Q=D^m t^b,\qquad C=D^m t^A s.
```
The compressed map has coefficients $`(t^b,t^A s,D)`$, the same signed seed,
and the same divisibility guard. Its divisions cost one original raw step;
its affine operations cost $`m+1`$. This is variable-clock transport, not a
one-step conjugacy. Positive clock coverage and both adjacent endpoint
bounds recover every original raw time, as proved in
[full-time compression](../QCD.TimeCompression.002/README.md).

If $`u\ge v`$, the actual coefficient height
$`\max\{|Q|,|C|\}`$ strictly decreases. If $`b>0`$, the compressed map is
in [the previously proved family](../QCD.CommonBase.002/README.md).
If $`b=0`$, its multiplier is one and its nonzero signed offset is divisible
by $`D`$. Legal initial divisions give an exact permanent affine tail;
this closes the remaining child without an orbit assumption.

## QCD.CommonBase.003.2 — quantitative full-raw escape and sign

For a signed seed $`n\ne0`$ and an integer $`M\ge0`$, define
```math
B(M)=\begin{cases}
2|n|+M+1,&b=0,\\ |n|+(|n|+1+MD^{b/h})P_0,&b>0,
\end{cases}
```
where, in the positive-remainder case,
$`h=\gcd(b,v)`$ and $`P_0=b/h+v/h`$. Every raw time satisfying
```math
B(M)(m+1)\le r
```
has $`M<|F^r(n)|`$. Also $`r\ge B(0)(m+1)`$ implies $`sF^r(n)>0`$.
These estimates include all initial divisions and all raw intermediate
states; they do not infer a full-sequence limit from a selected subsequence.

## QCD.CommonBase.003.3 — exact multi-division events and rays

Whole-base order means $`n=t^k w`$ with $`t\nmid w`$, not prime valuation
or a unit-residual decomposition. At a normalized phase $`k<v`$, one affine
operation is followed by exactly $`\lfloor(k+u)/v\rfloor`$ forced divisions.
The new phase is $`(k+u)\bmod v`$, and the physical event clock is
```math
1+\lfloor(k+u)/v\rfloor.
```
After $`i`$ such events, the same original raw orbit has physical clock
$`i+\lfloor(k+iu)/v\rfloor`$.

For $`g=\gcd(u,v)`$, set
```math
T=t^g,\quad U=u/g,\quad V=v/g,\quad
A_0=\lfloor a/g\rfloor,\quad S=t^{a\bmod g}s.
```
This leaves all coefficients and raw guards exactly unchanged. Every
normalized rebased phase $`k<V`$ has sweep clock and increment
```math
P=U+V=(u+v)/g,\qquad
\beta_k=S T^{A_0-U-V+1+k}\sum_{j=0}^{V-1}T^j.
```
For every nonzero signed seed there are a legal division prefix $`r_0\le|n|`$,
a phase $`k<V`$, and its endpoint $`x`$, with $`|x|\le|n|`$, such that
```math
F^{r_0+jP}(n)=x+j\beta_k\qquad\text{for every }j\ge0.
```
Each sweep has $`V`$ affine edges and $`U`$ division edges and preserves
that phase. The clock $`P`$ is not a cycle period when $`s\ne0`$.
The formal ray statements also permit $`s=0`$, without asserting escape.

## QCD.CommonBase.003.4 — periodic points

A nonzero return would repeat arbitrarily late, contradicting the full-raw
escape estimate. Thus the only periodic point is zero, including for signed
negative seeds and offsets. This conclusion requires $`s\ne0`$.

## Examples and boundaries

For $`(Q,C,D)=(8,32,4)`$,
```math
1\longmapsto40\longmapsto10\longmapsto112\longmapsto28\longmapsto7.
```
There are two affine operations and three divisions: the sweep clock is five
and its increment is six. The second affine operation requires two consecutive
divisions; the old one-or-two-step event would lose a raw instruction.

At exponent equality, $`(Q,C,D)=(4,16,4)`$ has the raw orbit
```math
1\longmapsto20\longmapsto5\longmapsto36\longmapsto9,
```
with sweep clock two and increment four. Its compressed map is additive.

Sign alignment cannot be omitted from the intermediate norm estimate.
For $`(Q,C,D)=(8,4096,4)`$,
```math
-767\longmapsto-2040\longmapsto-510\longmapsto16\longmapsto4\longmapsto1.
```
An estimate asserting the initial magnitude is below every later magnitude
would fail here. The proof uses late compressed endpoint bounds, and the
replay applies the local norm estimate only after sign alignment.

The uniform offset threshold cannot be lowered by one: the previously proved
boundary instance $`(Q,C,D)=(2,4,4)`$, at $`a=u+v-1`$, has primitive raw cycle
$`1,6,16,4,1`$.

The result concerns positive $`D`$, pure common-base $`Q`$, positive $`u,v`$,
and $`a\ge u+v`$. Negative divisors, nontrivial signed residual multipliers
in $`Q=p^u r`$, and other offset regimes are separate statements. The
canonical prime-source discussion intersects this result at
$`\varepsilon=1`$, $`r=1`$, now for both exponent orderings. Its prime/unit
hypotheses are not used to justify the stronger composite whole-base result.

## Implementations

Three Lean modules contain **27 supporting and conclusion theorems**, not
27 distinct source claims. They prove the signed additive child, exact
coefficient reconstruction and height decrease, compressed and original
raw budgets, full-sequence escape and sign, periodicity, legal multi-division
events, residual sums, sweep clocks, gcd rebasing, and same-seed prefix recovery.
The default build includes these modules and the template examples.

The exact signed Go checker reconstructs both coefficient presentations,
replays two complete legal raw sweeps, and checks all guards, phases, branch
counts and increments. Its finite sample checks **7432128 certificates**,
not distinct maps or orbits. It covers original bases two through nine,
$`1\le u,v\le8`$ with arbitrary ordering and gcd, three offset exponents,
sixteen signed residuals, 256 ordinary signed seeds, and forced-phase controls.

`Configure` rejects parameters outside $`2\le t\le9`$, $`1\le u,v\le8`$,
$`u+v\le a\le256`$, and $`0<|s|\le8`$. `CheckSeed` rejects nil,
unconfigured, zero, or greater-than-512-bit seeds. These are execution limits,
not theorem hypotheses. Nine tests cover both orderings, equality, the named
ray, 402-bit signed division prefixes, refusals, multiple divisions, the
alignment counterexample, and the exact finite count. Zero warmed replay
allocations are measured only on seven prepared configurations. Coefficient
setup and arbitrary-size performance are not included in that claim.
Finite replay does not replace the universal proofs.

```sh
make lean
CGO_ENABLED=0 go test -count=1 ./QCD.CommonBase.003/go
CGO_ENABLED=0 go vet ./QCD.CommonBase.003/go
make go GOFILE=QCD.CommonBase.003/go/CommonBaseGeneralHighOffset.go
make tex TEXFILE=QCD.CommonBase.003/tex/CommonBaseGeneralHighOffset.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
