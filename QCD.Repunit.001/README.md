<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Repunit divisors and the unit cycle

`QCD.Repunit.001` studies the raw map

\[
T_{q,D}(n)=\begin{cases} n/D, & D\mid n,\\ qn+1, & D\nmid n,\end{cases}
\]

on the slice where the divisor is the repunit sum \(D=S_k(q)=1+q+\cdots+q^{k-1}\).
The offset is one, so the affine branch is \(n\mapsto qn+1\) and the divisor
identity \((q-1)S_k=q^k-1\) makes \(S_k\) a divisor of \(q^k-1\). For
\(q\ge2\) the family proves that the multiplicative order of \(q\) modulo
\(S_k\) is exactly \(k\), that the seed \(1\) runs a positive cycle of minimal
period \(k\) through the states \(S_2,\dots,S_k\), that the residue walk from
\(0\bmod S_k\) visits \(k\) distinct residues and repeats with period \(k\),
that \(0\) is the only state sent to \(0\), and that the unit-offset return map
fixes \(1\).

All statements are about \(\mathbb{N}\) and the raw clock: one division or one
affine step is one instruction, and no compressed clock is used.

## Claims

| # | Claim | Lean |
| --- | --- | --- |
| .1 | The repunit sum \(S_k=1+q+\cdots+q^{k-1}\) satisfies \(S_0=0\), \(S_{k+1}=S_k+q^k\), \(S_1=1\) and \(qS_k+1=S_{k+1}\). | `RepunitSumZero`, `RepunitSumSucc`, `RepunitSumOne`, `RepunitSumSuccMul` |
| .2 | Addition rule \(S_{j+k}=S_j+q^jS_k\), and \(S_k=q^{k-1}+S_{k-1}\) for \(k\ge1\). | `RepunitSumAdd`, `RepunitSumEqPowAdd` |
| .3 | Divisor identity: \((q-1)S_k=q^k-1\) and \(S_k\mid q^k-1\) for \(q\ge1\). | `RepunitSumMulPred`, `RepunitSumDvdPred` |
| .4 | Power congruence \(q^k\equiv1\pmod{S_k}\) for \(q\ge1\). | `RepunitSumModeq` |
| .5 | Growth: \(1\le S_k\) and \(0<S_k\) for \(k\ge1\); for \(q\ge2\) the sequence \(S_k\) is strictly increasing, \(S_k<S_{k+1}\), and \(S_k<q^k\), indeed \(S_k+1\le q^k\). | `RepunitSumOneLe`, `RepunitSumPos`, `RepunitSumLtSucc`, `RepunitSumStrictMono`, `RepunitSumSuccLePow`, `RepunitSumLtPow` |
| .6 | Exact order: for \(q\ge2\) and \(0<j<k\) one has \(q^j\not\equiv1\pmod{S_k}\), so the order of \(q\) modulo \(S_k\) is \(k\). | `RepunitSumModeqOrder` |
| .7 | Branch rules and the last-step decomposition of an iterate. | `RepunitStepOfDvd`, `RepunitStepOfNotDvd`, `RepunitIterateSuccLast` |
| .8 | Zero is a fixed and absorbing trap of the slice, and no state other than zero is sent to zero. | `RepunitStepZero`, `RepunitStepIterateZero`, `RepunitStepEqZero` |
| .9 | Unit cycle: for \(q\ge2\), \(k\ge1\) and \(j<k\) the iterate of the seed \(1\) is \(T^{\,j}(1)=S_{j+1}\), the return \(T^{\,k}(1)=1\) holds, and no earlier positive time returns \(1\) to itself. | `RepunitStepIterateOne`, `RepunitStepIterateOneCycle`, `RepunitStepIterateOneNe` |
| .10 | Return map \(R(n)=(q^{\,k-1}n+S_{k-1})/S_k\): after \(k-1\) affine events from \(1\) the state is \(S_k\), and the division returns \(1\), so \(R(1)=1\) for \(k\ge2\). | `RepunitReturnFixesOne` |
| .11 | Residue walk \(r\mapsto(qr+1)\bmod S_k\): the state at time \(j\) is \(S_j\bmod S_k\), it is periodic with period \(k\), and the first \(k\) residues \(S_0,\dots,S_{k-1}\) are pairwise distinct. | `RepunitResidueIterateZero`, `RepunitResidueIteratePeriod`, `RepunitResidueIterateInjective` |

Its definitions are `RepunitSum`, `RepunitStep`, `RepunitResidue` and
`RepunitReturn`.

## Reduction and recovery record

**Original obligation.** Compute, on the offset-one slice with divisor
\(D=S_k(q)\) and \(q\ge2\), the multiplicative order of \(q\) modulo \(D\),
the positive cycle of the seed \(1\) together with its minimal period, the
accessible residues of the residue walk, and the trap state. The wider
classification of the positive orbits of the slice is a separate obligation
and is listed as open below.

**Replacement obligations.** (i) the divisor identity \((q-1)S_k=q^k-1\);
(ii) the exact order of \(q\) modulo \(S_k\); (iii) the orbit of the seed \(1\)
and its minimal period; (iv) the residue walk of \(1\bmod S_k\); (v) the trap
set of the slice; (vi) the unit-offset return map.

**Recovery.** Each replacement obligation is a statement about the raw map
\(T_{q,S_k}\) or about its residue dynamics \(r\mapsto qr+1\bmod S_k\). The
orbit formula .9 lists the cycle states \(1,S_2,\dots,S_k\) in order, so the
periodic point and its period are explicit; .5 separates the repunit sums, so
the listed states are distinct, and .6 shows that no positive exponent
\(j<k\) satisfies \(q^j\equiv1\pmod{S_k}\), so the period is minimal.
The residue walk .11 identifies the accessible residues
\(\{0,S_1,\dots,S_{k-1}\bmod S_k\}\) and shows that the walk returns to itself
after \(k\) steps, so no residue outside that set is reached from \(0\); .8
shows that \(0\) is a fixed point of the map, so it is not a positive periodic
point. Divisibility of \(q^k-1\) by \(S_k\) is used only through the exact
identity \((q-1)S_k=q^k-1\).
The return map .10 recovers the same cycle from the entry data of the affine
run.

**Difficulty decrease.** The infinite orbit-classification problem is replaced
by a finite order computation in \(\mathbb{Z}/S_k\mathbb{Z}\) of size \(k\)
together with a closed list of cycle states. The decreasing resource is the
number of affine events between two divisions, which is \(k-1\) on the cycle
and bounded by one order computation.

**Preservation conditions.** \(k\ge1\) in .2 and .5; \(q\ge1\) in .3 and
.4; \(q\ge2\) in .5, .6, .9 and .11, and in the orbit clause of .10, whose
return identity \(R(1)=1\) holds for \(q\ge1\); \(k\ge1\) in .9; \(k\ge2\) in
.10. The claims hold at the raw clock, with no compression, and they are
statements about every positive seed of the slice only where stated. The
strict decrease of accessible states under the return map, the eventual-trap
statement for non-captured orbits, the density-one eventual affine escape of
the complement of the returned set, the logarithmic entry bound of the
contracting core, the statement that every return-map cycle lies in
\([0,c]\), the general modulus, the Hull–Dobell condition, the criticality
ledger, the classical isolation and the general offset are not formalized here
and remain open obligations of companion families.

## Controls

- \(q=1\): the divisor identity degenerates to \(0=0\) and \(q^j\equiv1\pmod{k}\)
  for every \(j\), so the order claim is false and the rows that use it assume
  \(q\ge2\).
- \(k=1\): \(S_1=1\) makes every state divisible by the divisor, so the map is
  the identity and the cycle has length \(1\); the return row assumes \(k\ge2\).
- A divisor that is not a repunit sum, for instance \(q=2\), \(D=5\): the raw
  orbit of the seed \(1\) does not return to \(1\) within the tested horizon.
  The residue walk from \(0\) does return, since \(0\mapsto1\mapsto3\mapsto2
  \mapsto0\) is a cycle of the affine residue map.
- The classical instance \(q=3\), \(k=2\), \(D=S_2=4\): the cycle is
  \(1\mapsto4\mapsto1\).

## Formal dependencies

`GeneralizedCollatz` supplies `Iterate` and `IterateAdd`; the module imports
`Mathlib.Algebra.BigOperators.Ring.Finset` for the sum, `Mathlib.Data.Nat.ModEq`
for the congruences and `Mathlib.Order.Monotone.Basic` for strict monotonicity.

## Go certificate contract

`go/RepunitDivisor.go` checks the slice over the grid \(q=2,\dots,20\) and
\(k=1,\dots,20\), with trap states \(n\le200\), in seven slices. The divisor
slice runs over \(k=1,\dots,20\); the order, cycle, residue, trap and return
slices over \(k=2,\dots,20\); the controls consist of the order witnesses at
\(q=1\) for \(k=2,\dots,20\), the divisor-one identity on \(2\le q\le20\) and
\(0\le n\le10\), and the twenty-four-step non-repunit walk at \(q=2\) with
divisor five. The six parallel slices are chunked over the multiplier and the
controls run in a single pass.

| Slice | Checks | Content |
| --- | --- | --- |
| divisors | 760 | \((q-1)S_k=q^k-1\) and \(S_k\mid q^k-1\) |
| order | 3971 | \(q^k\equiv1\) and \(q^j\not\equiv1\) for \(0<j<k\) |
| cycle | 7581 | orbit of \(1\), its states, and minimality |
| residues | 12274 | residue walk, period and distinctness |
| traps | 72561 | \(T(n)=0\iff n=0\) for \(n\le200\) |
| returns | 722 | return map fixing \(1\) |
| controls | 442 | \(q=1\) witnesses that break the order claim, \(k=1\), and a non-repunit divisor |

The printed total is 98311 checks. The sweeps run in `math/big` with reusable
workspace buffers and four chunked workers over the `q` range; the allocation
test measures a warmed `StepBig` walk and observes zero allocations per step
after the buffers have reached the walk width. `go/RepunitDivisor_test.go` recomputes
the sums by Horner's rule, the steps and the order by independent references,
and pins every slice count and the total, so the printed certificate cannot
drift silently. The grid is a finite certificate of agreement, not a proof of
the universal statements above.

## Build and checks

```
make lean
make go GOFILE=QCD.Repunit.001/go/RepunitDivisor.go
CGO_ENABLED=0 go vet ./QCD.Repunit.001/go
CGO_ENABLED=0 go test -count=1 ./QCD.Repunit.001/go
make tex TEXFILE=QCD.Repunit.001/tex/RepunitDivisor.tex
```
