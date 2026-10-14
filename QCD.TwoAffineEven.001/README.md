<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Two-affine closure at even length

Let $`q,a,b,n,y`$ be positive integers satisfying
```math
qn+1=2^a y,\qquad qy+1=2^b n.
```

**Classification.** If $`a+b=2t`$, then necessarily
```math
a=b=t,\qquad q=2^t-1,\qquad n=y=1.
```
Conversely, these values solve both equations for every $`t\ge1`$.
The theorem includes unequal components in its hypotheses and excludes them in its conclusion; no assumption $`n=y`$ is needed.

## Proof

Interchange the two letters and components so that $`a\le b`$.
Then $`a\le t`$. Elimination gives
```math
\delta n=q+2^a,\qquad \delta=2^{2t}-q^2>0.
```
Put $`A=2^t`$. Since $`q<A`$ and $`A-q`$ is a positive integer,
```math
\delta\le\delta n=q+2^a\le q+A\le(A-q)(A+q)=\delta.
```
All inequalities are equalities. Hence $`n=1`$, $`a=t`$, $`q=A-1`$, and the original equations give $`b=t,y=1`$.

The length $`a+b`$ is the binary shortcut length. The unit solution repeats a single odd block; it is not a primitive cycle with two distinct odd states.

[Detailed proof](tex/TwoAffineEven.tex) ·
[Complete classification](lean/TwoAffineClassification.lean) ·
[Equal-component identities](lean/TwoAffineEven.lean)
