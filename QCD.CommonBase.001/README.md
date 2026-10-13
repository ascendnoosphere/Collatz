<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Common-base super-offset escape

[Detailed proofs](tex/CommonBaseHighOffset.tex) ·
[Whole-base order and legal events](lean/CommonBaseHighOffset.lean) ·
[Phase kernel](lean/CommonBaseHighOffsetKernel.lean) ·
[Raw clocks and rays](lean/CommonBaseHighOffsetClock.lean) ·
[Initial divisions](lean/CommonBaseHighOffsetNormalization.lean) ·
[Full raw escape](lean/CommonBaseHighOffsetEscape.lean) ·
[Periodicity and threshold](lean/CommonBaseHighOffsetOutcomes.lean) ·
[Exact finite replay](go/CommonBaseHighOffset.go) ·
[Tests](go/CommonBaseHighOffset_test.go)

Let $t,u,v,a\in\mathbb N$ and $s\in\mathbb Z$ satisfy
$$
t\ge2,\qquad 0<u<v,\qquad \gcd(u,v)=1,\qquad a\ge u+v,\qquad s\ne0.
$$
Set $Q=t^u$, $D=t^v>0$, and $C=t^a s$. The raw signed map is
$$
F(n)=\begin{cases}n/D,&D\mid n,\\Qn+C,&D\nmid n.\end{cases}
$$
The base may be composite. Neither $\gcd(s,t)=1$ nor $t\nmid s$ is required.
The statements concern every signed seed, not a density-one set. Negative
**seeds and offsets** are allowed; negative **divisors** are not covered here.
The sub-offset, intermediate and critical offset regimes are separate families.

## QCD.CommonBase.001.1 — legal phase sweeps and exact raw rays

For a nonzero state, whole-base order $k$ means
$n=t^k w$ with $t\nmid w$; it is not a prime valuation.
After a legal initial division prefix of length $r_0\le|n|$, there is a
state $x=t^k w$, $0\le k<v$, with $|x|\le|n|$.
Each normalized event performs one raw affine instruction and then zero or one
legal division. Its phase is $(k+u)\bmod v$.

Write $G_v(t)=\sum_{j=0}^{v-1}t^j$. Coprimality makes the successive phases
$(k+iu)\bmod v$, $0\le i<v$, a permutation. The $v$ events have exactly
$u$ divisions, raw length $P=u+v$, and translation
$$
\beta_k=s\,t^{a-u-v+1+k}G_v(t).
$$
For every $j\in\mathbb N$, at the same original seed,
$$
F^{r_0+jP}(n)=x+j\beta_k.
$$
Every translated state retains phase $k$, so the formula can be iterated
without imposing a new guard condition.

## QCD.CommonBase.001.2 — effective full-sequence escape and sign

Every nonzero signed seed escapes in magnitude along the **entire raw orbit**.
For all $M,r\in\mathbb N$,
$$
|n|+(|n|+1+M D^u)(u+v)\le r\quad\Longrightarrow\quad |F^r(n)|>M.
$$
For every $r\ge |n|+(|n|+1)(u+v)$, one also has
$sF^r(n)>0$. Thus all nonzero orbits eventually have the offset's sign.
These are effective integer-value bounds; no polynomial bit-complexity claim
is made.

Sign alignment is essential to the intermediate-state estimate. If a normalized
state $x=t^k w$ satisfies $sx\ge0$, then every raw future state $z$ obeys
$$
t^k|z|\ge|x|,\qquad D^u|z|\ge|x|.
$$
This estimate is not applied before alignment. For $(Q,C,D)=(2,8,4)$, the
raw block $-5,-2,4,1$ refutes the unqualified estimate.

## QCD.CommonBase.001.3 — the only periodic point

Zero is fixed because division has priority. Every nonzero seed has no positive
raw return, so zero is the only periodic point and its primitive period is one.
This follows from full-sequence escape: a positive return would repeat beyond
its own escape budget.

## QCD.CommonBase.001.4 — the threshold cannot uniformly be lowered

At $a=u+v-1$, the instance $(t,u,v,a,s)=(2,1,2,2,1)$ has
$(Q,C,D)=(2,4,4)$ and the primitive positive raw cycle
$$
1\longrightarrow6\longrightarrow16\longrightarrow4\longrightarrow1.
$$
Consequently replacing $a\ge u+v$ by $a\ge u+v-1$ cannot yield a universal
escape theorem for this parameter family. No classification of the entire
critical regime is inferred from this one exact obstruction.

## Concrete controls and reduction

For $(Q,C,D)=(9,243,27)$, with $(t,u,v,a,s)=(3,2,3,5,1)$,
$$
1\longrightarrow252\longrightarrow2511\longrightarrow93
\longrightarrow1080\longrightarrow40.
$$
Here $\beta_0=39$, $P=5$, and the next sweep endpoint is $79$.
For the composite-base case $(t,u,v,a,s)=(4,1,3,4,2)$,
$$
32\longrightarrow640\longrightarrow10\longrightarrow552\longrightarrow2720.
$$
Both the residual two and the offset residual two share a prime with the base;
whole-base order remains valid. Here $k=2$, $\beta_2=2688$, and $P=4$.

The original obligation is to classify every signed seed in the stated
super-offset family. The replacement consists of a finite initial division
prefix, a phase in $\{0,\ldots,v-1\}$, an explicit geometric kernel, and
signed arithmetic progression growth. The initial prefix terminates by strict
magnitude descent. The high-offset condition eliminates leading-order
cancellation; coprimality closes the finite phase sweep. The aligned magnitude
estimate and clock coverage recover every raw time, with the displayed finite
budget. This proves a solvable parameter subclass, not a reduction that hides
an unresolved infinite-orbit assertion in its coefficients.

## Exact finite certificates and resource contracts

The Go program checks two actual raw sweeps for each selected seed. It verifies
all branch guards, whole-base orders, division counts, $u+v$ clocks and
translation endpoints; it checks the magnitude inequality only after alignment.
The main grid uses $2\le t\le9$, $2\le v\le8$, coprime $0<u<v$,
$u+v\le a\le u+v+2$, and $-8\le s\le8$ with $t\nmid s$.
Seeds include the nonzero integers from $-128$ through $128$, and all
phases $t^k w$, $k<v$, with $-8\le w\le8$, $t\nmid w$.
The reference count is 2,186,784 two-sweep certificates, not distinct orbits.
Separate controls include offsets $\pm3\cdot2^{204}$, opposite signs,
a divisible offset residual, the zero exception and the threshold cycle.

`Configure` refuses inputs outside its mathematical and finite resource
contract: $2\le t\le9$, $0<u<v\le8$, coprimality, $u+v\le a\le256$,
and $0<|s|\le8$. It does not require $t\nmid s$. The reserved seed bit
limit is $\max(8,(v-1)\operatorname{BitLen}(t)+4)$. Unconfigured workspaces,
mismatched exponents, nil or oversized seeds and zero are refused.
A resource refusal is not a counterexample to the theorem. Reusable disjoint
buffers and cached powers avoid warmed replay allocations on the four tested
configurations; arbitrary-size performance is not asserted. These finite
certificates do not replace the universal Lean and mathematical proofs.

```sh
make lean
CGO_ENABLED=0 go test -count=1 ./QCD.CommonBase.001/go
CGO_ENABLED=0 go vet ./QCD.CommonBase.001/go
make go GOFILE=QCD.CommonBase.001/go/CommonBaseHighOffset.go
make tex TEXFILE=QCD.CommonBase.001/tex/CommonBaseHighOffset.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
