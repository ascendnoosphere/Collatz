<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Exact uniform-cylinder checking

Status: **CLOSED OBLIGATION** for the 31 listed direct certificates and the
two legs of the $`111/103`$ join. Their local identities and smaller-parent
comparisons are checked without sampling the parameter. This does not prove
that their source families cover the residual.

## Retained implementation

The checker is in [SwarmChecks.go](../go/SwarmChecks.go), with the complete
certificate table and negative controls in
[SwarmChecks_test.go](../go/SwarmChecks_test.go). Run from the repository root:

```sh
CGO_ENABLED=0 go test -count=1 ./QCD.SwarmAttack.001/go
```

`CheckCylinder(source, modulus, target, slope, word)` accepts a nonempty
binary word and nonnegative 64-bit coefficients, with source, modulus, and
target strictly positive. Its contract is

```math
T^h(a+Mt)=b+Nt\qquad\text{for every integer }t\ge0.
```

The public coefficients are bounded by the input type. Every intermediate
coefficient uses `math/big`, so an intermediate orbit state may exceed
64 bits without overflowing. Restricted parameter classes are represented
by substituting $`t=r+Lu`$ before calling the checker, provided the resulting
input coefficients fit in 64 bits. Arbitrary finite parameter ranges and
coverage predicates are outside this API.

## Why acceptance proves the identity

Maintain the exact prefix identity $`T^j(a+Mt)=A_j+C_jt`$, initially with
$`(A_0,C_0)=(a,M)`$. Before accepting the next letter $`e_j`$, require
$`C_j`$ even and $`A_j\equiv e_j\pmod2`$. These conditions fix the branch
for every parameter, not merely a finite sample. Then update

```math
(A_{j+1},C_{j+1})=(A_j/2,C_j/2)\quad\text{if }e_j=0,
```

```math
(A_{j+1},C_{j+1})=((3A_j+1)/2,3C_j/2)\quad\text{if }e_j=1.
```

The guards make these divisions exact. Induction proves legality and the
prefix identity at every tick. The final coefficient comparisons
$`A_h=b`$ and $`C_h=N`$ prove the requested identity. Positivity follows
from the positive starting ray and the positive shortcut branches.

`CheckDirectCylinder` adds $`b<a`$ and $`N\le M`$. Thus
$`(a+Mt)-(b+Nt)=(a-b)+(M-N)t>0`$ throughout the ray, proving strict descent.
An expanding identity may pass `CheckCylinder` while failing this stronger
contract.

## Executed cases and controls

The test table contains the eight initial direct cylinders, the twenty-one
further direct cylinders, and the two deep cylinders, including
$`27+2^{59}t\mapsto23+3^{37}t`$. All 31 pass `CheckDirectCylinder`.
The two identities

```math
T(111+2^{15}3^7t)=167+2^{14}3^8t
=T^{12}(103+2^{26}t)
```

pass `CheckCylinder`. Since $`103<111`$ and $`2^{26}<2^{15}3^7`$, the
second source is a positive smaller parent for every $`t\ge0`$.

The controls reject a changed endpoint, changed endpoint slope, changed
word, changed source, insufficient source modulus, a parameter-dependent
parity guard, zero coefficients forbidden by the contract, an empty word,
and a nonbinary letter. The genuine identity $`T^3(3+8t)=4+9t`$ passes the
identity checker and fails the descent checker. A valid thinner cylinder
and a trajectory whose intermediate value exceeds 64 bits both pass.

The original report referred to a larger temporary verifier at
`/tmp/opencode/Agent16/Verifier.go` and its output file. Neither is retained.
The current claims refer only to the implementation and tests linked above;
the temporary tool's broader API, coverage tables, and output are not
presented as independently reproducible results.
