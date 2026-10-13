# Signed core bound

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

Let $`A`$, $`B`$ and $`m`$ be natural numbers with $`A<m`$, and write
$`N=\lfloor B/(m-A)\rfloor`$. This family proves the integer estimate that
makes a finite invariant core possible. If a map $`H\colon\mathbb{Z}\to\mathbb{Z}`$
satisfies $`m\,|H(n)|\le A\,|n|+B`$ at every integer, then every state outside
the radius contracts, every state inside the radius stays inside it, every
orbit enters the radius after finitely many steps, and every orbit is
eventually periodic. The estimate is the bound used to close a signed core
once a return map is known to obey it. The return map itself is not
constructed here.

| # | Statement | Carried by |
| --- | --- | --- |
| .1 | The radius is $`N=\lfloor B/(m-A)\rfloor`$, and the remainder leaves one more copy of the gap: $`B<(m-A)(N+1)`$. | `CoreRadius`, `CoreBoundRoom` |
| .2 | Outside the radius the linear form contracts: $`n\ge N+1`$ implies $`An+B<mn`$. | `CoreDescentNat` |
| .3 | Inside the radius the same form stays below the next shell: $`n\le N`$ implies $`An+B<m(N+1)`$. | `CoreInvariantNat` |
| .4 | A map obeying $`m\,\lvert H(n)\rvert\le A\,\lvert n\rvert+B`$ contracts outside the radius and preserves it. | `CoreMapDescent`, `CoreMapInvariant` |
| .5 | Every orbit enters the radius after finitely many steps. | `CoreEntry` |
| .6 | Once inside, every later state remains inside. | `CoreStays` |
| .7 | **Eventual periodicity.** Every orbit admits a time $`t`$ and a positive period $`p`$ such that, for every $`k\ge 0`$, the state at time $`t+k`$ equals the state at time $`t+k+p`$. | `CoreEventuallyPeriodic` |

## Reduction and recovery record

**Original obligation.** Prove that a signed integer map obeying the linear
core bound has a finite invariant interval and that every orbit is eventually
periodic.

**Replacement obligations.** (i) Prove the room inequality for the remainder
of $`B`$. (ii) Deduce strict contraction outside the radius and the shell
bound inside it. (iii) Transfer both statements to absolute values of an
arbitrary integer map obeying the bound. (iv) Obtain entry by induction on
the absolute value, closure of the interval by induction on the clock, and
eventual periodicity by the pigeonhole principle on the $`2N+1`$ integers of
absolute value at most $`N`$.

**Recovery.** The statements are proved for every map
$`H\colon\mathbb{Z}\to\mathbb{Z}`$ satisfying the bound at every integer, with
the original absolute value and the original iteration clock. No state is
removed and no clock is compressed. Specializing $`H`$ to a concrete return
map is valid exactly when that map is shown separately to obey the bound; this
family does not supply that identification.

**Difficulty decrease.** The dynamics of an arbitrary map is replaced by one
linear comparison of natural numbers. Entry is ordinary induction on a
strictly decreasing natural number, and periodicity is a finite pigeonhole
followed by shifting one equality. Both are solved completely, including the
zero gap obstruction: the hypothesis $`A<m`$ keeps the divisor positive.

**Preservation conditions.** The inequality $`A<m`$ is required and is not
relaxed. The bound must hold at every integer, not merely on the orbit under
consideration, because the inductive step applies it to the successor. Nothing
is claimed about a map that exceeds the bound, and nothing is claimed about
the first time a raw orbit meets a zero residue.

## Controls

- With $`A=2`$, $`B=7`$ and $`m=3`$ the radius is $`7`$. At $`n=8`$,
  $`2\cdot8+7=23<24=3\cdot8`$, so the state contracts. At $`n=7`$,
  $`21<3\cdot8`$, so the state remains in the shell. The floor quotient of
  both $`8`$ and $`-8`$ is $`7`$.
- With $`A=0`$, $`B=5`$ and $`m=1`$ the radius is $`5`$ and the shell bound is
  $`5<6`$. The gap is the whole modulus.
- With $`A=3`$, $`B=5`$ and $`m=4`$ the gap is $`1`$ and the radius equals
  $`B`$. The first state outside it, $`n=6`$, satisfies $`3\cdot6+5<4\cdot6`$.

## Formal dependencies

`GeneralizedCollatz` supplies `Iterate` and `IterateAdd`. The module imports
`Mathlib.Data.Int.Basic` and `Mathlib.Data.Fintype.Pigeonhole`.

Not formalized here, and not consequences of the bound alone: the hitting time
of a zero residue, the identification of $`H`$ with one exact division of an
affine block, the values of $`A`$ and $`B`$ as maxima over residues, traps,
and every classical convergence statement.

## Go certificate contract

`go/SignedCore.go` checks the room, descent and invariance inequalities for
$`0\le A\le 8`$, gaps $`1\le m-A\le 8`$ and $`0\le B\le 24`$, at every natural
$`n\le 40`$, and checks the floor quotient on the seeds $`-12,\dots,12`$.
The largest product evaluated is $`mn=16\cdot 40=640`$. The largest value of
$`An+B`$ is $`344`$. Both fit in an `int64`. Quotient contraction is sampled
only for radii $`N\le 11`$, because those seeds satisfy $`|n|\le 12`$. For a
larger radius every such seed lies in the shell. The comparison
$`m\lfloor(A|n|+B)/m\rfloor\le A|n|+B`$ is the division identity for that
nonnegative quotient, not a separate estimate.

| Slice | Checks | Content |
| --- | --- | --- |
| core bound | 165600 | room, descent, invariance, the division identity, and the quotient split |
| controls | 8 | the three boundary triples above |

The printed total is 165608 checks. `go/SignedCore_test.go` recomputes the
radius, the room, the descent and shell values, and the quotient pairs with
`math/big`, and compares those integers with the pairs the checker evaluates.
It also pins the total. The grid is a finite certificate of agreement and not
a proof of the universal statements above.
