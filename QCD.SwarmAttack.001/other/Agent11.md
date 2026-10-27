<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Positive odd-return cycles with six to nine states

Status: **CLOSED OBLIGATION** for ranks six to nine, by an exhaustive finite
check with a proved search window. The earlier claims through ranks 40 and
1000 are withdrawn: their numerator estimate used an incorrect geometric sum.
The retained result does not exclude divergent positive orbits or cycles of
arbitrary rank.

## Exact cycle criterion

A rank-$`r`$ cycle consists of positive odd integers $`x_1,\ldots,x_r`$ and
positive exponents $`a_1,\ldots,a_r`$ satisfying
$`2^{a_i}x_{i+1}=3x_i+1`$ cyclically. Repeated listings of a shorter cycle are
allowed. Write

```math
A=\sum_{i=1}^r a_i,\qquad s_j=\sum_{i=1}^j a_i,\qquad
C=\sum_{j=0}^{r-1}3^{r-1-j}2^{s_j},\qquad D=2^A-3^r,
```

where $`s_0=0`$. Composing the edges gives $`Dx_1=C`$.

A positive exponent word defines a positive odd cycle exactly when
$`D>0`$ and $`D\mid C`$. Necessity follows from the displayed identity.
For sufficiency, let $`C_i`$ be the numerator for the cyclic rotation starting
at $`a_i`$. Expansion gives

```math
3C_i+D=2^{a_i}C_{i+1}.
```

Since $`D`$ is odd, divisibility propagates from $`C_1`$ to every $`C_i`$.
Each $`C_i`$ is positive and odd. Thus $`x_i=C_i/D`$ is a positive odd
integer, the transport identity gives every edge, and cyclic rotation closes
the list. Because the endpoint is odd, each exponent is the exact power of
two dividing $`3x_i+1`$.

## A complete finite search window

If one state equals one, its outgoing equation is
$`2^{a_i}x_{i+1}=4`$. Oddness forces $`a_i=2`$ and $`x_{i+1}=1`$;
propagation gives the repeated unit cycle. Every other cycle has $`x_i\ge3`$.
Multiplying the edge equations and cancelling the product of the states gives

```math
3^r<2^A=\prod_{i=1}^r\left(3+\frac1{x_i}\right)
\le\left(\frac{10}{3}\right)^r.
```

For each rank below, integer comparisons
$`3^r<2^A`$ and $`2^A3^r\le10^r<2^{A+1}3^r`$ leave exactly the stated
value of $`A`$. No floating-point logarithm determines the window.

| Rank $`r`$ | Total $`A`$ | $`D`$ | Positive compositions | $`D\mid C`$ |
|---:|---:|---:|---:|---:|
| 6 | 10 | 295 | 126 | 0 |
| 7 | 12 | 1909 | 462 | 0 |
| 8 | 13 | 1631 | 792 | 0 |
| 9 | 15 | 13085 | 3003 | 0 |

The number of positive compositions is $`\binom{A-1}{r-1}`$. The checker
visits every such marked word, without identifying cyclic rotations, and
tests $`C\bmod D`$. All 4383 tests fail divisibility. Hence a cycle at any
of these four ranks must be the repeated unit cycle. Together with the
[existing at-most-five result](../../QCD.ThreeAffineClosure.001/README.md),
this excludes non-unit positive cycles with at most nine listed odd states.

## The rejected bound

The earlier argument bounded every rotated numerator by

```math
C_i\le2^{A-r}\sum_{j=0}^{r-1}3^{r-1-j}2^j
=2^{A-r}(3^r-2^r).
```

That equality is correct. Replacing its right side with
$`2^A(1-(2/3)^r)`$ is not: already for $`r=2`$, the two factors multiplying
$`2^{A-r}`$ are $`5`$ and $`20/9`$. Consequently $`C_i<2^A`$,
$`x_i<2^A/D`$, and the proposed forced exponent
$`A=\lceil r\log_2 3\rceil`$ were not established. The rank-40 and
rank-1000 conclusions depended on those steps and have been removed.
The finite search above uses only the valid product window.

## Reproduction and scope

From the repository root:

```sh
make go GOFILE=QCD.SwarmAttack.001/go/SwarmChecks.go
CGO_ENABLED=0 go test ./QCD.SwarmAttack.001/go
```

The tests check the composition counts and include a positive control: at
rank six and total exponent twelve, the repeated unit word passes divisibility.
For the accepted ranks and totals, every numerator is smaller than
$`9\cdot3^8\cdot2^{18}<2^{34}`$; the checker therefore uses exact
64-bit integers without overflow. This is an executed finite computation,
not a Lean proof. Cycles of rank at least ten and universal capture remain
outside this result.
