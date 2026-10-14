<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Three-affine closure and exact odd recovery

Let $`a,b,c,q`$ be positive integers. Set

```math
K=a+b+c,\qquad
\Delta=2^K-q^3,\qquad
B=q^2+q2^a+2^{a+b}.
```

There exist positive odd integers $`x,y,z`$ satisfying

```math
2^a y=qx+1,\qquad 2^b z=qy+1,\qquad 2^c x=qz+1
```

**if and only if** $`q`$ is odd, $`\Delta>0`$, and $`\Delta\mid B`$.

[Lean criterion and recovery](lean/ThreeAffineLegal.lean) ·
[Elimination identity](lean/ThreeAffineClosure.lean) ·
[Detailed proof](tex/ThreeAffineClosure.tex)

## Proof and reconstruction

Write

```math
U=q^2+q2^b+2^{b+c},\qquad
V=q^2+q2^c+2^{c+a}.
```

Direct expansion gives the three transport identities

```math
qB+\Delta=2^aU,\qquad
qU+\Delta=2^bV,\qquad
qV+\Delta=2^cB.
```

For necessity, an odd state and a positive division exponent force $`q`$
odd. Eliminating the three states gives $`\Delta x=B`$.
Since $`x>0`$ and $`B>0`$, the determinant is positive and divides $`B`$.

Conversely, suppose the three arithmetic conditions hold.
The determinant is odd, so it is coprime to each power of two.
The first transport identity gives $`\Delta\mid U`$, and the second gives
$`\Delta\mid V`$. Define

```math
x=B/\Delta,\qquad y=U/\Delta,\qquad z=V/\Delta.
```

These quotients are positive integers. Each numerator and the determinant
is odd, so all three states are odd. Dividing the transport identities by
$`\Delta`$ recovers the three equations. Oddness of the next state proves
the exact valuations

```math
v_2(qx+1)=a,\qquad v_2(qy+1)=b,\qquad v_2(qz+1)=c.
```

Thus one fixed parameter word reduces to three explicit arithmetic tests
and reconstructs a unique ordered triple. It does not require a search for
three simultaneous state witnesses.

## Clocks and examples

The closed word has three odd-return ticks, $`K`$ shortcut ticks, and
$`K+3`$ raw ticks. These are return lengths, not automatically primitive
periods: a word can repeat a shorter cycle.

For $`q=5`$ and $`(a,b,c)=(1,1,5)`$,

```math
\Delta=3,\quad (B,U,V)=(39,99,249),\quad (x,y,z)=(13,33,83).
```

The odd-return cycle is $`13\to33\to83\to13`$.

Oddness of the multiplier is essential. With $`q=2`$ and
$`(a,b,c)=(1,2,1)`$, the determinant $`8`$ divides $`B=16`$,
but the first equation gives $`y=5/2`$. Determinant divisibility alone
is not sufficient without the stated parity hypothesis.

For arbitrary integer states, the elimination theorem still gives
$`\Delta x=B`$ and the rotated identities without imposing positivity or
oddness. The legal criterion is a separate stronger statement for the
positive odd class. It supplies no uniform bound on $`K`$ or classification
of all three-letter parameter words.
