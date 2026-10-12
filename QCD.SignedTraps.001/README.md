# Signed trap itineraries

<!-- SPDX-License-Identifier: CC-BY-4.0 -->

The raw map of the library sends

\[
n\longmapsto \begin{cases} n/d, & d\mid n,\\ qn+c, & d\nmid n,\end{cases}
\qquad q,c,n,d\in\mathbb{Z},\ d\ne0,
\]

and a state is *trapped* when no iterate of it is divisible by \(d\). On a
trapped orbit the divisor never acts, the orbit follows the single affine
recursion \(n\mapsto qn+c\), and the multiplier alone decides its future. This
family proves that classification over \(\mathbb{Z}\), so negative states,
negative divisors and alternating signs are covered: the offset sum is a
geometric series, the \(j\)-th state is \(q^{j}n+c\,(1+q+\dots+q^{j-1})\), a
zero multiplier reaches the constant offset, a unit multiplier translates or
stays fixed, the negative unit multiplier runs the reflection pair
\(n\mapsto c-n\), an expanding multiplier is fixed exactly on the affine
fixed-point equation and otherwise escapes every bound in absolute value.
Independently, the family identifies divisibility with a walk on
\(\mathbb{Z}/m\mathbb{Z}\), \(m=|d|\): a raw orbit is trapped exactly when the
residue walk \(r\mapsto qr+c \bmod m\) avoids the zero class at every time. That
converts the infinite divisibility question into avoidance of the origin by a
deterministic finite walk, and it is the premise used by every companion family
whose hypotheses ask for a division-free orbit.

| # | Statement | Carried by |
| --- | --- | --- |
| .1 | The offset sum \(T_j(q)=q^0+\dots+q^{j-1}\) satisfies the shifted geometric series \((q-1)T_j(q)=q^{j}-1\). | `TrapSum`, `TrapSumMulSubOne` |
| .2 | One-step recursion: \(T_{j+1}(q)=q\,T_j(q)+1\). | `TrapSumRec` |
| .3 | Two-step extension: \(T_{j+2}(q)=T_j(q)+q^{j}+q^{j+1}\). | `TrapSumAddTwo` |
| .4 | Degenerate multipliers: \(T_{j+1}(0)=1\), \(T_j(1)=j\), \(T_{2j}(-1)=0\) and \(T_{2j+1}(-1)=1\). | `TrapSumZero`, `TrapSumOne`, `TrapSumNegOneEven`, `TrapSumNegOneOdd` |
| .5 | A state the divisor does not divide executes the affine branch exactly: \(T(n)=qn+c\). | `RawStepAffine` |
| .6 | Trapping is preserved: if no iterate divides, the successor of a state does not divide either. | `NeverDividesShift` |
| .7 | **Affine itinerary.** On a trapped orbit the \(j\)-th state is \(q^{j}n+c\,T_j(q)\). | `NeverDividesIterateAffine` |
| .8 | A zero multiplier reaches the constant offset: for \(j\ge1\) the \(j\)-th state is \(c\). | `TrapZeroConstant` |
| .9 | With a zero multiplier the offset \(c\) is itself a trapped fixed point. | `TrapZeroFixed` |
| .10 | A unit multiplier translates: the \(j\)-th state is \(n+jc\). | `TrapOneTranslation` |
| .11 | A unit multiplier with nonzero offset escapes: for every target \(R\) some state exceeds \(R\) in absolute value. | `TrapExistsNatAbove`, `TrapOneUnbounded` |
| .12 | The negative unit multiplier returns after an even number of steps and reflects after an odd number: \(T^{2j}(n)=n\) and \(T^{2j+1}(n)=c-n\). | `TrapNegOneEven`, `TrapNegOneOdd` |
| .13 | The reflection is a genuine two-cycle: \(T(n)=c-n\) and \(T(c-n)=n\). | `TrapNegOneTwoCycle` |
| .14 | **Fixed point.** A state the divisor does not divide is fixed exactly when \((q-1)n+c=0\). | `TrapFixedIff` |
| .15 | **Expanding multiplier.** If \(|q|\ge2\) and \((q-1)n+c\ne0\), the orbit escapes: for every target \(R\) some state exceeds \(R\) in absolute value. | `TrapExpandingEscape` |
| .16 | **Residue walk.** The affine branch modulo \(m=|d|\) is \(r\mapsto qr+c\), and along a trapped prefix the residue walk is the cast of the raw orbit. | `ResidueStepZ`, `CastIterateOfPrefix` |
| .17 | Along a trapped orbit the cast identity holds at every time. | `NeverDividesCastIterate` |
| .18 | **Dichotomy.** A raw orbit is trapped exactly when its residue walk avoids the zero class at every time. | `ResidueAvoidsZeroIffNeverDivides` |

## Reduction and recovery record

**Original obligation.** Decide the dynamics of the raw map on an orbit that
never divides, and decide divisibility itself, over the signed integers with an
arbitrary nonzero divisor.

**Replacement obligations.** (i) Prove the closed form of the affine itinerary
on a trapped orbit, including the offset sum and its recursion. (ii) Prove the
orbit description for each multiplier case: zero reaches the constant offset
and the offset is a fixed point; one translates, with the fixed case \(c=0\);
negative one is the reflection pair; an expanding multiplier is fixed exactly
on the affine fixed-point equation and otherwise escapes. (iii) Prove that
escaping means exceeding every real, hence every integer, bound in absolute
value. (iv) Identify the affine branch modulo \(|d|\) as a walk on
\(\mathbb{Z}/m\mathbb{Z}\), compare it with the orbit cast along a trapped
prefix, and prove the dichotomy with the zero class.

**Recovery.** Every statement is about the original signed raw map `RawStep`
and its iterates at the raw clock. No state space is changed, no clock is
compressed, and no state is removed: the only hypothesis is the trapping
premise itself, which is exactly the hypothesis of the classification. The
dichotomy is an equivalence, so it transfers in both directions: a trapped
orbit yields an avoiding residue walk, and an avoiding residue walk yields a
trapped orbit.

**Difficulty decrease.** On a trapped orbit the signed dynamics collapses to a
one-parameter affine recursion whose coefficient is the multiplier, so the
infinite family of maps is decided by four multiplier cases, and the
divisibility predicate of a signed map becomes a deterministic finite walk on
the residue set \(\mathbb{Z}/m\mathbb{Z}\) of size at most \(|d|\). The escape
statements assume no trajectory bound: they are proved from the closed form and
the Archimedean property of the integers, with the integer division step
supplying the exact quotient in the divisible case.

**Preservation conditions.** The multiplier cases are exhaustive over
\(\mathbb{Z}\): \(q=0\), \(q=1\), \(q=-1\) and \(|q|\ge2\). The units of
\(\mathbb{Z}\) are exactly \(\pm1\), which is why the degenerate cases are
these two and why they are proved separately from the expanding case. All
statements are one-sided: nothing is claimed about an orbit that divides at
some time, and the certificate skips such walks instead of asserting the
classification on them.

## Controls

- The map is not the classical one. With \(q=2\) and \(c=1\) the affine branch
  is \(2n+1\), so the orbit of \(9\) with divisor \(3\) is
  \(9,3,1,3,1,\dots\) and not \(9,3,1,4,\dots\); the certificate checks both
  the orbit and the inequality \(T(9)\ne 2\cdot9+1\).
- With \(q=0\) and \(c=0\) the trapping premise is satisfied at \(n=7\), \(d=3\)
  and the walk becomes \(7,0,0,\dots\): the constant offset is reached after
  one step, and the offset \(0\) is a fixed point.
- With \(q=1\), \(c=0\) and \(d=5\) the state \(-4\) is fixed, and with \(q=1\)
  and \(c\ne0\) the orbit translates without bound, so no fixed point exists
  beyond \(c=0\).
- With \(q=-1\) and \(c=0\), \(d=7\) and \(n=5\) the orbit is the reflection
  pair \(5,-5,5,-5,\dots\); at \(n=0\) the pair degenerates to the fixed point
  \(0\).
- With \(q=2\), \(c=-4\) and \(d=3\) the state \(4\) lies on the affine
  fixed-point equation \((q-1)n+c=0\) and the trapped orbit is constant, while
  \(n=25\) is trapped and escapes; the certificate checks both.
- With \(d=1\) every state is divisible, so the trapping premise is empty and
  the orbit is constant; the certificate checks that walk and records the
  skips, so the classification is never asserted on a walk that divides.

## Formal dependencies

`GeneralizedCollatz` supplies the parameter record `Parameters`, the raw step
`RawStep` and the iterate `Iterate` with `IterateAdd`. The module imports
`Mathlib.Data.Int.Basic`, `Mathlib.Data.ZMod.Basic`,
`Mathlib.Logic.Function.Iterate` and `Mathlib.Algebra.Order.Ring.Abs` for the
signed, modular and absolute-value statements; `Mathlib.Tactic.Omega` is not
imported separately.

The following statements are *not* formalized here and remain open obligations
of companion families: the density statements of the signed families, the
first-division return map with its residue-dependent exponent, the signed core
certificate with its boundary bound, the forced prime-power classification of
the independent base, the criticality ledger, and every convergence statement
for the classical target.

## Go certificate contract

`go/SignedTraps.go` checks finite instances of the statements over the grid
\(|q|\le6\) and \(0\le j\le24\) for the offset sums, \(|q|\le4\),
\(|c|\le4\) and the six signed divisors \(\pm2,\pm3,\pm5\) with the ten signed
seeds \(-13,-7,-3,-1,0,1,2,6,11,25\) over \(24\) steps for the walks, and the
moduli \(2,\dots,12\) for the residue map. The signed arithmetic is exact
`int64`: the largest offset sum is below \(6^{24}<2^{63}\), and the orbit
sweep stays below \(4^{24}\cdot30<2^{59}\); the test file re-checks both
bounds.

| Slice | Checks | Content |
| --- | --- | --- |
| offset sums | 1010 | geometric series, recursion, two-step extension, degenerate multipliers |
| itinerary | 99872 | affine formula and residue cast on every division-free prefix |
| classification | 18464 | multiplier cases on every division-free walk |
| residues | 6237 | affine residue map against the cast of the step |
| controls | 125 | documented boundary cases of the section above |

The printed total is 125708 checks. The sweeps run with a shared orbit buffer,
chunk the multiplier range over four workers, and the allocation test measures
a warmed walk and observes zero allocations per run. `go/SignedTraps_test.go`
recomputes the offset sums from the closed form with `math/big`, the steps with
a big-integer reference, checks the residue range and the documented orbits,
and pins every slice count and the total. The grid is a finite certificate of
agreement and not a proof of the universal statements above.

## Build and checks

```
make lean
make go GOFILE=QCD.SignedTraps.001/go/SignedTraps.go
CGO_ENABLED=0 go vet ./QCD.SignedTraps.001/go
CGO_ENABLED=0 go test -count=1 ./QCD.SignedTraps.001/go
make tex TEXFILE=QCD.SignedTraps.001/tex/SignedTraps.tex
```
