<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# QCD.Relations.Cycles.001 — Explicit cycles and the power-of-d intersection

## Statement and domain

Fix natural numbers \(d\ge2\), \(q\ge1\), \(c\ge0\) and let
\[
T_{q,c,d}(n)=
\begin{cases}
n/d, & d\mid n,\\
qn+c, & d\nmid n,
\end{cases}
\qquad n\in\mathbb{N},
\]
the raw generalized Collatz map with divisor \(d\). Write \(T^{k}\) for \(k\)
instructions, so \(T^{0}\) is the identity and \(T^{k+1}=T\circ T^{k}\). All
statements are over \(\mathbb{N}\) and all divisions are exact where written.

The family records four parameter slices of the raw map and proves, on each, a
cycle or divergence statement together with one intersection statement.

1. At \(d=2\) and \(q=2c+1\): an odd state always takes the affine branch;
   for even \(c\) the affine branch returns an odd state, and every positive
   seed of that slice first reaches an odd state and then passes every bound.
   For odd \(c\) the gcd with \(c\) is a step invariant, so the strata of
   \(c\) are invariant, and bounded orbits are periodic inside their own
   stratum.
2. The geometric-offset slice \(c=3(8^{h}-1)/7\), \(q=2c+1\) at \(d=2\):
   the seed \(3\) runs a primitive cycle of length \(3h+1\) that avoids \(1\).
3. The full-residue-access slice
   \(c=(d-1)(d^{k-1}-1)\), \(q=(d-1)d^{k-1}+1\) for \(d\ge2\), \(k\ge2\):
   the seed \(d-1\) runs a primitive cycle of length \(k+1\), which avoids
   \(1\) once \(d\ge3\); at \(d=k=2\) this is the classical cycle
   \(1\mapsto4\mapsto2\mapsto1\).
4. The intersection slice \(q=d+1\), \(c=d-1\) for \(d\ge3\): a positive
   state reaches \(1\) exactly when it is a power of \(d\), and no positive
   iterate of the map returns \(1\) to itself.

Claims 1 and 2 share the divisor \(2\) and the multiplier \(2c+1\), so they are
stated as one slice; claims 3 and 4 are independent slices. Every claim is a
statement about the raw map, not about a normalized clock: the iterates counted
below are instructions of \(T\), including every division.

## Numbered results

| # | Claim | Lean |
| --- | --- | --- |
| .1 | Branch rules: a multiple of \(d\) is divided immediately, a non-multiple takes the affine branch. | `RawStepOfDvd`, `RawStepOfNotDvd` |
| .2 | Iterate decomposition: the first instruction may be executed separately, and so may the last; \(j\) divisions send \(d^{j}m\) to \(m\) and \(d^{j}\) to \(1\) for \(d\ge2\). | `RawStepIterateSucc`, `RawStepIterateSuccLast`, `RawStepDivMulIterate`, `RawStepPowIterate` |
| .3 | A bounded orbit repeats one of its states: if every iterate of \(n\) is at most \(M\), then \(T^{\,k+p}(n)=T^{\,k}(n)\) for some \(k\) and some \(p>0\). | `RawStepBoundedEventuallyPeriodic` |
| .4 | At \(d=2\) an odd state takes the affine branch; with \(q=2c+1\) this is \((2c+1)n+c\), so for even \(c\) the result is odd again, and for \(1\le c\) it exceeds \(n\). | `RawStepTwoOfOdd`, `RawStepTwoEvenOffsetAffine`, `RawStepTwoEvenOffsetOddOfOdd`, `RawStepTwoEvenOffsetIncreaseOdd` |
| .5 | Every positive seed of the slice \(q=2c+1\), \(d=2\) reaches an odd state. | `RawStepTwoEvenOffsetReachesOdd` |
| .6 | Even-offset divergence: for even \(c\ge1\) and every positive seed, the orbit passes every bound. | `RawStepTwoEvenOffsetUnbounded` |
| .7 | Odd-offset gcd invariance: for odd \(c\) and \(q=2c+1\), \(\gcd(T(n),c)=\gcd(n,c)\), and the same holds for every iterate. | `RawStepTwoOddOffsetGcd`, `RawStepTwoOddOffsetGcdIterate` |
| .8 | Odd-offset stratum cycles: for odd \(c\), a bounded orbit has a periodic point in its own stratum, if no positive seed diverges then every divisor \(g\) of \(c\) occurs as \(\gcd(y,c)\) of a periodic point \(y\), and for \(c>1\) the seed \(c\) never reaches \(1\). | `RawStepTwoOddOffsetStratumCycle`, `RawStepTwoOddOffsetManyCycles`, `RawStepTwoOddOffsetSeedNoCapture` |
| .9 | The offset \(c_h=3(8^{h}-1)/7\) is an integer, and with \(q_h=2c_h+1\) it satisfies \(7c_h=3(8^{h}-1)\) and \(3q_h+c_h=3\cdot2^{3h}\). | `SevenDvdEightPowSubOne`, `CycleC`, `CycleQ`, `CycleCMulSeven`, `CycleQIdentity` |
| .10 | On the slice of .9 the seed \(3\) takes the affine branch: \(T(3)=3\cdot2^{3h}\). | `CycleAffineStep` |
| .11 | Orbit formula: \(T^{\,j+1}(3)=3\cdot2^{3h-j}\) for \(j\le3h\). | `CycleIterateFormula` |
| .12 | The seed \(3\) returns to itself after \(3h+1\) instructions, no earlier positive time returns it, and the orbit meets \(1\) at no time. | `CycleReturns`, `CyclePrimitive`, `CycleAvoidsOne` |
| .13 | Full-residue-access slice: for \(d\ge2\) and \(k\ge2\) the multiplier exceeds \(d\) exactly by the offset, \(q=d+c\), the affine step of \(d-1\) lands on \((d-1)d^{k}\), and \(d\) does not divide \(d-1\). | `FullAccessQeq`, `FullAccessIdentity`, `FullAccessNotDvd`, `NatPowDvdSelfPow` |
| .14 | Orbit formula: \(T^{\,j+1}(d-1)=(d-1)d^{k-j}\) for \(j\le k\). | `FullAccessIterateFormula` |
| .15 | The seed \(d-1\) returns to itself after \(k+1\) instructions and no earlier positive time does, and for \(d\ge3\) its orbit meets \(1\) at no time. | `FullAccessReturns`, `FullAccessPrimitive`, `FullAccessAvoidsOne` |
| .16 | At \(d=k=2\) the slice of .13 is the classical cycle \(1\mapsto4\mapsto2\mapsto1\), and the orbit formula of .14 is the branch form \(T^{\,j+1}(1)=2^{2-j}\) for \(j\le2\). | `FullAccessClassicalInstance`, `FullAccessIterateFormula` |
| .17 | Zero is fixed by every raw map. | `RawStepZero` |
| .18 | Intersection slice: for \(d\ge3\) a state whose image is \(d^{m}\) is \(d^{m+1}\). | `RawStepIntersectionPredecessor` |
| .19 | Iterate formula: for \(d\ge3\), \(k\) instructions from a positive \(x\) land on \(d^{t}\) only from \(x=d^{k+t}\). | `RawStepIntersectionIteratePow` |
| .20 | For \(d\ge3\) and positive \(x\), \(x\) reaches \(1\) exactly when \(x\) is a power of \(d\). | `RawStepIntersectionReachesOne`, `RawStepIntersectionReachesOneIff` |
| .21 | For \(d\ge3\) no positive power of the clock returns \(1\) to itself. | `RawStepIntersectionNoReturnToOne` |

Claims .12, .15 and .21 are statements about primitive returns: an orbit that
returns at time \(3h+1\), respectively \(k+1\), does not return earlier, and
the intersection slice excludes every return of \(1\) to itself at positive
time.

The full-residue-access slice of .13–.16 shows that full residue access does
not by itself single out the classical target: at \(d=k=2\) the cycle is
\(1\mapsto4\mapsto2\mapsto1\), while for \(d\ge3\) the displayed cycle avoids
\(1\) by .15, so the two slices have different targets.

## Reduction and recovery

**Original obligation.** For the four parameter families above, exhibit the
cycle, prove its length, prove that no shorter return occurs, decide whether
the cycle meets \(1\), and for the intersection family decide which positive
seeds reach \(1\). The obligation is a per-family claim: the cycles are given
by explicit parameter pairs, and no uniform statement about arbitrary
parameters is made.

**Replacement obligations.** Seven finite obligations replace the argument, all
over \(\mathbb{N}\) with explicit hypotheses: (i) the branch rules and the
iterate decomposition of the raw map; (ii) the arithmetic identity
\(7\mid 8^{h}-1\) and the closed form of the geometric offset; (iii) the closed
orbit formula of each cycle family, of the form
\(T^{\,j+1}(x)=K\cdot2^{m-j}\), respectively \(K\cdot d^{m-j}\); (iv) the
minimality of the return, read off from the formula; (v) the parity dichotomy
at \(d=2\), which separates even offsets, where the affine branch keeps states
odd and increasing, from odd offsets, where the gcd with \(c\) is invariant;
(vi) the stratum statement obtained by combining invariance with the pigeonhole
principle for a bounded positive orbit; (vii) the intersection predecessor
lemma, where an affine step is shown to miss every power of \(d\).

**Recovery.** Each recovery step is an implication inside \(\mathbb{N}\).
Given the orbit formula, the return at time \(3h+1\) is \(3\cdot2^{0}=3\) and
every earlier positive time gives \(3\cdot2^{e}\) with \(e\ge1\), which is at
least \(6\) and hence not \(3\); similarly for \(k+1\) and \(d-1\), where
\((d-1)d^{e}\ge d-1\) is an equality only for \(e=0\). The avoidance of \(1\)
follows because \(3\cdot2^{e}\ge3\) and \((d-1)d^{e}\ge d-1\ge2\) for
\(d\ge3\), \(e\ge0\). The stratum statement uses divisibility rather than
equality: \(\gcd(T(n),c)=\gcd(n,c)\) transports the stratum of the periodic
point back to the stratum of the seed. For the intersection family, the
predecessor lemma is the only step that needs arithmetic beyond
\(\mathbb{N}\): at a non-multiple of \(d\) the affine value modulo \(d+1\) is
\(-2\), while the powers of \(d\) modulo \(d+1\) are \(\pm1\), so parity
separates the two sides: an even exponent would force \(d+1\mid3\) and an odd
exponent \(d+1\mid1\), both impossible for \(d\ge3\). Inducting the lemma
over the number of remaining steps
gives .19, and \(t=0\) gives .20.

**Difficulty decrease.** The infinite objects of the original obligation are
replaced by closed formulas indexed by \(h\), \(k\), \(d\). Each family is
exhausted by one induction whose step is a division or an affine application,
so no search, no compactness argument and no limit is required; minimality and
avoidance of \(1\) follow from monotonicity of the exponent rather than from a
separate orbit enumeration. The intersection slice is reduced to one
\(\mathbb{Z}/(d+1)\)-computation plus an induction over the step count.

**Preservation conditions.** Every statement keeps its parameters in the
stated range: \(d=2\) with \(q=2c+1\) in .4–.8, where .6 additionally assumes
that \(c\) is even and \(c\ge1\), and .7, .8 assume \(c\) odd; \(h\ge0\) with
\(7\mid 8^{h}-1\) in .9–.12; \(d\ge2\), \(k\ge2\) in .13–.15, with \(d\ge3\)
only for the avoidance of \(1\); \(d\ge3\) in .18–.21. The iteration count is
the raw instruction count in every claim, so no normalization, no shortcut
step and no renumbering of the clock is involved.

## Controls and excluded cases

- \(d=2\) in .15: the slice sends \(1\mapsto4\mapsto2\mapsto1\), so the orbit
  of the seed \(1\) does meet \(1\); the hypothesis \(d\ge3\) is exactly what
  excludes it.
- \(d=2\) in .20: the seed \(3\) reaches \(1\) through
  \(3\mapsto10\mapsto5\mapsto16\mapsto8\mapsto4\mapsto2\mapsto1\) without being a
  power of \(2\), so the hypothesis \(d\ge3\) is necessary.
- \(c=0\): .17 gives the fixed point \(0\), and at \(d=2\), \(q=1\) the state
  \(1\) is also fixed, since the affine branch is the identity; the hypothesis
  \(1\le c\) in .6 excludes this degeneration.
- Odd \(c\) in .6: with \(q=2c+1\) an odd state maps to an even state when
  \(c\) is odd, so the alternation of odd states is lost. The odd-offset slice
  carries the corresponding positive statement instead, namely the gcd
  invariance of .7.
- \(h=0\) in .9–.12: the offset vanishes, \(q=1\), and the cycle of \(3\) has
  length \(1\); the slice is not excluded, but the parity statement recorded in
  the certificate's first sweep is asserted only for \(h\ge1\).
- \(k=1\) in .13–.15: the formalized statements carry \(2\le k\). At
  \(k=1\) the offset vanishes and the slice degenerates to the two-step cycle
  \(d-1\mapsto d(d-1)\mapsto d-1\), which those statements do not cover.
- \(c=1\) in .8: the seed of the last clause is \(c\) itself, so the
  hypothesis \(1<c\) is necessary; for \(c=3\) the walk of the seed stays
  inside the stratum of \(3\) and never meets the stratum of \(1\).

## Formal dependencies

`Foundations.Main.StartHere` supplies `Iterate` with `Iterate f 0 x = x` and
`Iterate f (n+1) x = f (Iterate f n x)`, and `IterateAdd`. The family restates
the two iterate decomposition rules it uses as `RawStepIterateSucc` and
`RawStepIterateSuccLast`, so it does not depend on any other content folder.
Mathlib supplies `ZMod` for the congruence computation of
`RawStepIntersectionPredecessor`, together with `Nat.gcd_add_mul_right_left`,
`ZMod.natCast_eq_natCast_iff'`, `Even.neg_one_pow` and `Odd.neg_one_pow`.

## Go certificate contract

`go/RelationsCycles.go` checks the statements above on bounded ranges with
exact integer arithmetic, and `go/RelationsCycles_test.go` re-derives the
values on sampled parameters with independently allocated `math/big` operands.
The program prints

```
relations cycles checks: 3229604, failures: 0
```

and exits nonzero on any failure. The total decomposes as
\(4370+11935+569964+2600000+43335\):

- geometric-offset sweep, \(0\le h\le30\): divisibility of \(3(8^{h}-1)\) by
  \(7\), the identity \(3q+c=3\cdot2^{3h}\), the closed orbit formula at every
  time up to \(3h+1\), the return at \(3h+1\), the absence of an earlier
  return and the absence of \(1\), plus the parity of the offset for
  \(h\ge1\);
- full-residue-access sweep, \(2\le d\le40\), \(2\le k\le12\):
  \(q=d+c\), the residue \(q\equiv c\equiv1\pmod d\), the identity
  \(q(d-1)+c=(d-1)d^{k}\), the closed orbit formula, minimality of the return,
  the classical instance at \(d=k=2\), and the avoidance of \(1\) for
  \(d\ge3\);
- intersection sweep, \(3\le d\le40\), seeds \(1\le x\le599\), times
  \(0\le j\le24\): the equivalence "state \(1\) at time \(j\) exactly for
  \(x=d^{j}\)", the absence of a return of \(1\) to itself at positive time,
  and the control at \(d=2\);
- even-offset sweep, even \(2\le c\le20\), seeds \(1\le n\le2000\): every seed
  reaches an odd state within \(64\) instructions and then stays odd and
  strictly increases for \(64\) further instructions;
- odd-offset sweep, odd \(1\le c\le41\), seeds \(1\le n\le2000\): the gcd
  invariance of one instruction, the realization of every divisor of \(c\)
  as such a gcd, and, for \(c>1\), the walk of the seed \(c\) over \(64\)
  instructions without meeting \(1\).

The bounded sweeps are certificates of agreement, not proofs; the Lean
statements above are the proofs. The sweeps of the first four families run in
`math/big`, so no orbit is observed through a wrapped word; the odd-offset
sweep evaluates one instruction per gcd case in `uint64`, with seeds at most
\(2000\) and multipliers at most \(83\), so every value recorded there stays
below \(2^{18}\), and its seed-capture walk runs in `math/big` because those
states grow. `TestSweepTotals`
pins the printed total and its per-slice decomposition, `TestStepMatchesReference`
and `TestStepBigMatchesReference` compare the step functions with independent
references at machine and at large states, `TestCycleSliceTriples`,
`TestFullAccessResiduesAndIdentity`, `TestFullAccessOrbitAndMinimality`,
`TestIntersectionEquivalence` and `TestIntersectionControlAtTwo` re-derive the
four parameter slices of the family,
`TestEvenOffsetGrowthControl` and `TestOddOffsetGcdControl` re-derive the
dichotomy together with its \(c=0\) and even-\(c\) controls, and compare
states on both sides of the divisor with the reference,
`TestOddOffsetSeedCapture` re-derives the seed-capture claim with the
\(c=1\) control,
`TestWarmedOrbitAllocation` requires zero allocations on a multi-word walk
once its buffers have grown to the walk width, and
`TestDocumentedRanges` checks the \(2^{18}\) bound and the wide-state claim of
this paragraph.

## Build and checks

```
make lean
make go GOFILE=QCD.Relations.Cycles.001/go/RelationsCycles.go
CGO_ENABLED=0 go vet ./QCD.Relations.Cycles.001/go
CGO_ENABLED=0 go test -count=1 ./QCD.Relations.Cycles.001/go
make tex TEXFILE=QCD.Relations.Cycles.001/tex/RelationsCycles.tex
```

The Lean module is `QCD.Relations.Cycles.001/lean/RelationsCycles.lean` and is
part of the default build target. The Go program is a `main` package with no
external dependency; its tests are in the same directory. The TeX document
`tex/RelationsCycles.tex` restates the numbered results with the same
hypotheses and the same Lean names in its correspondence table.
