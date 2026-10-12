<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# QCD.Additive.002 — Complete positive additive cycle classification

For `c ≥ 1` and `D ≥ 2`, use the positive division-precedence raw map

```text
T(n) = n/D  if D divides n,
       n+c  otherwise.
```

Its first-division map contains all additions before exactly one division.
[QCD.Additive.001](../QCD.Additive.001/README.md) supplies access, guards,
finite-core capture and the original raw clock.

## Factor extraction and the exact window

There is a unique maximal divisor `t | c` coprime to `D`. Repeated gcd
removal constructs

```text
c = st,    gcd(t,D) = 1,    s | D^k  for some k ≥ 0.
g = gcd(c,D),    L = D/g,
N = floor(c(L−1)/(D−1)),    M = floor(t(L−1)/(D−1)).
```

Every positive raw cycle has a division-endpoint phase. All its endpoints
are multiples of `s` and lie at most `N`. For `x = sm`,

```text
x ≤ N  iff  m ≤ M,     M ≤ t.
```

No coprimality between `s` and `D` is assumed.

## Complete cycle correspondence

Take the permutation `m ↦ D^(-1)m mod t`, with positive representatives
`1,…,t`; the zero residue is represented by `t`, not zero. Keep exactly
those entire permutation orbits whose representatives all lie in `1,…,M`.

These surviving primitive orbits correspond to all positive primitive raw
cycles, up to cyclic starting phase. An edge `m → m'` has

```text
ell = (Dm'−m)/t,     0 ≤ ell < L,
T^[ell+1](sm) = sm'.
```

All earlier division guards fail. Concatenation preserves the exact raw
clock and least period. Conversely, a primitive raw return is shifted to
the finite core and segmented into first-division blocks with its original
total clock. Endpoint recognition recovers the same modular orbit.

For a primitive orbit `m₀,…,m_(h−1)`, its periods are

```text
H period = h = ord_(t/gcd(m₀,t))(D),
raw period = h + (D−1)(m₀+…+m_(h−1))/t,
1 ≤ h ≤ t ≤ c.
```

The grouped quotient is an integer; dividing its summands separately is
incorrect. The multiplicative order at modulus one is one.

## Boundary controls

- `c=10,D=6`: `s=2,t=5,M=2`. Representatives 1 and 2 give raw cycles
  `2→12→2` and `4→14→24→4`, of periods 2 and 3.
  Representative 3 is a scaling ghost: the proposed scaled start 6 immediately
  divides to 1.
- `c=5,D=2`: the modular orbit `(1,3,4,2)` has indices `(1,1,0,0)`
  and raw period `4+10/5=6`. Consecutive divisions are separate edges.
- `c=10,D=4`: `M=1`, but 1 maps to 4, so the entire orbit is rejected.
- `c=8,D=6`: `N=3` but `M=0`; a nonempty core can contain no cycle.
- `c=5,D=6`: the positive zero-class representative 5 has H period 1,
  effective modulus 1, and raw period 6.

## Reduction and computational costs

The original obligation is to enumerate every positive cycle without a seed
bound. The replacement is the finite permutation on `t` representatives
and its exact window test; both reconstruction directions and primitive-period
recovery are proved. The decreasing search resource is the finite catalogue:
each permutation visit consumes an unvisited representative, with at most
`t` visits and no unexamined cycles left afterward.

This is not a total runtime bound depending only on `t`. Preprocessing needs
at most `floor(log₂ s)` gcd-removal rounds and modular inversion. Big-integer
arithmetic and output copying have bit costs. The sum of lengths of the
surviving modular cycles is at most `t`; complete raw expansion can require
up to `tL` instructions. For `c=1`, its single H edge has raw period `D`,
however large `D` is.

## Formal proofs

[AdditiveCycles.lean](lean/AdditiveCycles.lean) proves:

- `AdditiveOffsetDecomposition` and `AdditiveCoprimeFactorMaximal`:
  factor extraction and divisibility-maximality;
- `AdditiveClosedPathSupported`, `AdditiveClosedPathCore`,
  `AdditiveScaledCoreIff`, and `AdditiveModularEdgeLegal`:
  necessity and sufficiency of the exact window and legal edge recovery;
- `AdditiveEndingCorePath` and `IterateReturnAlongCycle`:
  segmentation with the original total clock and phase-invariant return times;
- `AdditiveRawPrimitiveToModular` and `AdditiveModularPrimitiveRaw`:
  both primitive reconstruction directions and exact grouped raw period;
- `AdditiveResiduePermutationEdge` and `AdditivePositiveResidueUnique`:
  the unit permutation and its positive representative convention;
- `AdditivePrimitiveOrder`, `AdditivePrimitiveLengthBoundModulus`, and
  `AdditivePrimitiveLengthBound`: the exact effective order, the effective-modulus
  bound \(h\le t/\gcd(m_0,t)\), and the finite catalogue bound;
- `AdditiveRawPrimitiveClassification`: a single raw-to-modular witness
  carrying the original raw period, grouped clock, exact order, and length bound.

[Detailed proofs](tex/AdditiveCycles.tex) assemble the cycle correspondence
up to phase from these maps and endpoint recognition. No separate
phase-quotient API is defined. Zero offset and signed parameters are outside
this statement.

## Exact computation

[AdditiveCycles.go](go/AdditiveCycles.go) stores parameters, representatives,
effective moduli, and clocks as arbitrary-precision integers. The finite
enumeration budget and table indices are machine-sized. Capacity refusals
and callback interruptions are unfinished searches, never complete empty
answers. An empty window separately certifies no positive cycles.

`NewMap` owns copies of its parameters. `BuildCycle` snapshots inputs and
constructs an owned certificate, supporting direct input/output aliases;
`Verify` checks every edge, unique access index, early-return exclusion and
claimed field without changing its certificate. `Enumerate` uses private
`Cache` and `Workspace` buffers. Its callback receives a read-only borrowed certificate;
retain it only with a deep `CopyFrom`. Do not share these mutable buffers
between goroutines or shallow-copy `big.Int` storage. Enumeration preparation
reserves traversal buffers before its inner permutation loops. Certificates
and retained outputs have separate storage costs.

The executable checks 25,506 primitive cycles across all
`1 ≤ c ≤ 96`, `2 ≤ D ≤ 48`: 4,512 parameter pairs. Tests compare them with
independently extracted raw cycles throughout `1,…,cD`, scan marked
multiplicative orders independently, and exercise every claimed field,
malformed paths, whole-orbit filtering, ghosts, ownership, aliases, nil
validation, callback interruption, and huge arithmetic/budget boundaries.
A separate certificate has raw period `2^200`, checked algebraically without
raw replay. These finite executions test the implementation; the written and
formal arguments establish the universal cycle classification.

```bash
make lean
make go GOFILE=QCD.Additive.002/go/AdditiveCycles.go
CGO_ENABLED=0 go test ./QCD.Additive.002/go
CGO_ENABLED=0 go vet ./QCD.Additive.002/go
make tex TEXFILE=QCD.Additive.002/tex/AdditiveCycles.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
