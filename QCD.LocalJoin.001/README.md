<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# An exact raw Collatz join on one cylinder

For the **raw** classical map
```math
C(x)=\begin{cases}x/2,&x\equiv0\pmod2,\\3x+1,&x\equiv1\pmod2,\end{cases}
```
set, for every integer $t\ge0$,
```math
n=11003+1048576t,\qquad p=9915+944784t,\qquad j=16733+1594323t.
```

The complete legal prefixes satisfy
```math
C^{32}(n)=C^6(p)=33466+3188646t,\qquad C^{33}(n)=C^7(p)=j.
```
These are raw-step clocks: an odd affine step and its following division
count separately. The prefixes meet first at the displayed even state.

## Positive smaller parent

The exact gaps and a fixed contraction are
```math
n-p=1088+103792t,\qquad j-n=5730+545747t,
\qquad 0<p<n<j,\qquad 100p\le91n.
```
Thus capture of this particular parent implies capture of its source.
The replacement is well-founded, but it is not an exhaustive parent rule
and does not prove capture of either orbit.

## Complete prefixes and exclusions

The [article's coefficient table](tex/LocalJoin.tex) contains all forty
distinct affine forms in the two prefixes. It proves every branch
uniformly in $t$, rather than extrapolating from sampled orbits.

The only common forms are the two meeting states above.
No displayed state equals $8251+786432t$ or $24754+2359296t$.
The actual fourth source successor is $24758+2359296t$.

Both coefficients of $j$ are odd, so its parity is $t+1$ modulo $2$.
The next branch divides when $t$ is odd and is affine when $t$ is even;
the full cylinder has no single affine continuation beyond $j$.

## Proofs and checks

- [Detailed proofs](tex/LocalJoin.tex).
- [Lean proofs](lean/LocalJoin.lean): coefficient rules, all successor
  equalities, cross comparisons, exclusions, raw iterate clocks and contraction.
- [Exact Go checks](go/LocalJoin.go): coefficient legality and numerical
  prefixes, with overflow checks and parameter support $0\le t\le10^6$.
- [Tests](go/LocalJoin_test.go): boundary inputs, exclusions, first meetings
  and allocation-free verification.

Run from the repository root:
```sh
make lean
make tex TEXFILE=QCD.LocalJoin.001/tex/LocalJoin.tex
make go GOFILE=QCD.LocalJoin.001/go/LocalJoin.go
CGO_ENABLED=0 go test ./QCD.LocalJoin.001/go
```
