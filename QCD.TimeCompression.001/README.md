<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Common-power time compression

[Detailed proofs](tex/TimeCompression.tex) ·
[Formal proofs](lean/TimeCompression.lean) ·
[Exact arithmetic](go/TimeCompression.go) ·
[Arithmetic tests](go/TimeCompression_test.go)

Let
```math
F_{q,c,d}(n)=
\begin{cases}
n/d,&d\mid n,\\ qn+c,&d\nmid n,
\end{cases}
\qquad |d|\ge2.
```
Suppose
```math
q=d^aQ,
\qquad
c=d^aC,
\qquad
a\in\mathbb N,
```
and put $`G=F_{Q,C,d}`$.

## QCD.TimeCompression.001.1 — exact block expansion

Define
```math
\tau(n)=
\begin{cases}
1,&d\mid n,\\ a+1,&d\nmid n.
\end{cases}
```
Then
```math
F_{q,c,d}^{\,\tau(n)}(n)=G(n)
```
for every signed integer $`n`$. A division is unchanged. An affine instruction
has value
```math
qn+c=d^a(Qn+C),
```
so the next $`a`$ instructions in the selected block are forced divisions, and
after those instructions the state is $`Qn+C`$.

This is a variable-clock identity on the same state space. In general the
identity state correspondence does not intertwine the maps one step at a time.
For example,
```math
F_{4,4,2}(1)=8\ne2=F_{1,1,2}(1),
\qquad
F_{4,4,2}^{\,3}(1)=2.
```

## QCD.TimeCompression.001.2 — complete sampled trajectory

Let $`R(k,n)`$ count the affine instructions among the first $`k`$ steps of the
compressed orbit of $`n`$. The accumulated original time is
```math
T(k,n)=k+aR(k,n).
```
At every compressed time,
```math
G^k(n)=F_{q,c,d}^{\,T(k,n)}(n).
```
Thus no compressed state or initial seed is discarded, and every clock change is
explicit.

## QCD.TimeCompression.001.3 — returns and capture

For every $`k\in\mathbb N`$,
```math
F_{q,c,d}^{\,k+aR(k,n)}(n)=n
\quad\Longleftrightarrow\quad
G^k(n)=n.
```
Accordingly, a closed compressed itinerary with $`r`$ affine events expands to
a closed raw itinerary with exactly $`k+ar`$ instructions. This statement gives
the expanded return time; it does not silently identify primitive periods.

For an arbitrary target $`S\subseteq\mathbb Z`$, if every orbit of $`G`$ meets
$`S`$, then every orbit of $`F_{q,c,d}`$ meets the same target. The witness time
is $`T(k,n)`$. No target invariance, positivity, or unsigned-divisor assumption
is needed.

Let $`h(u,v)=\max\{|u|,|v|\}`$. The coefficient height satisfies
```math
h(q,c)=|d|^a h(Q,C).
```
If $`a>0`$ and $`(Q,C)\ne(0,0)`$, then $`h(Q,C)<h(q,c)`$, so removal of the
common power is a strict reduction in the intrinsic natural-number height.
When $`(Q,C)=(0,0)`$, the two coefficient pairs are identical and the theorem
is only an exact transport identity, not a strict reduction. Recovery is the
sampled-trajectory identity above. The remaining obligation is the corresponding
target problem for $`F_{Q,C,d}`$; no capture conclusion is assumed.

## Finite certificates and limits

The Go program compares every bounded block with the independent reference
model of $`F_{q,c,d}`$. Its grid is
```math
q,c\in\{-2,-1,0,1,2\},\quad d\in\{-4,-3,-2,2,3,4\},\quad
0\le a\le2,\quad -15\le n\le15,\quad 0\le k\le6,
```
and the sweep produces 97,650 certificates, each checking the exact endpoint,
the raw step count, the affine event count and the clock identity
$`\text{raw}=k+a\cdot(\text{affine events})`$. Arithmetic beyond fixed-width
integers and the rejected-parameter boundaries have separate tests. The finite
comparison illustrates the identities above and does not replace their proofs.
