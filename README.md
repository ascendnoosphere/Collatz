<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Generalized Collatz Library

## Raw map

For \(q,c,d\in\mathbb Z\) with \(|d|\ge2\), define
\[
F_{q,c,d}(n)=
\begin{cases}
n/d,&d\mid n,\\
qn+c,&d\nmid n.
\end{cases}
\]
The divisor retains its sign. Division has precedence, including at zero.
The classical raw map is \(F_{3,1,2}\).

## Foundations

[Definitions and theorems](Foundations.Main.StartHere/README.md) ·
[Detailed proofs](Foundations.Main.StartHere/tex/Foundations.tex) ·
[Formal proofs](Foundations.Main.StartHere/lean/GeneralizedCollatz.lean) ·
[Exact arithmetic](Foundations.Main.StartHere/go/Dynamics.go)

- A legal word is the unique raw itinerary of the same length.
- Chronological affine composition retains the full additive offset.
- Legal cycle closure implies \((Q-P)n=B\).
- For \(\Delta\ne0\),
  \[
  \frac{|\Delta|}{\gcd(|\Delta|,|b|)}\mid |c|
  \quad\Longleftrightarrow\quad
  \exists n\in\mathbb Z:\ \Delta n=cb.
  \]
  This scalar equation does not imply intermediate branch legality.
- Labelled graphs and marked systems form categories.
- A target-reflecting semiconjugacy transfers capture at the same time.
- A variable-clock semiconjugacy transfers forward capture at the accumulated time.

## Reductions

### Coprime scaling and offset normalization

[QCD.Scaling.001](QCD.Scaling.001/README.md) proves that coprime scaling preserves
the exact raw clock. If
\[
\gcd(|c|,|d|)=1,
\qquad c\mid q^k,
\]
then every signed integer orbit enters \(c\mathbb Z\) after at most \(k\) affine
events. From that entry onward it is exactly \(c\) times an orbit of
\(F_{q,1,d}\). This gives an all-seed capture equivalence for arbitrary targets,
with a positive-domain version when \(q\ge0\), \(c>0\), and \(d>0\).

### Common-power time compression

[QCD.TimeCompression.001](QCD.TimeCompression.001/README.md) proves the exact
variable-clock transport
\[
(q,c,d)=(d^aQ,d^aC,d)\longmapsto(Q,C,d).
\]
A compressed division costs one original raw step, while a compressed affine
event costs \(a+1\). After \(k\) compressed steps with \(r\) affine events, the
same state occurs at original raw time \(k+ar\). Compressed target capture
therefore recovers original target capture for every signed seed. If \(a>0\)
and \((Q,C)\ne(0,0)\), this is a strict reduction in the coefficient height
\(\max\{|q|,|c|\}\); the zero pair gives transport without strict decrease.

### Full-orbit recovery and primitive cycles

[QCD.TimeCompression.002](QCD.TimeCompression.002/README.md) recovers every raw
intermediate state in the common-power reduction, for all signed coefficients
and seeds with \(|d|\ge2\). Same-seed magnitude boundedness, full-sequence
magnitude escape and eventual periodicity are equivalent. Target capture is
bidirectional under the sufficient condition that the target retains each
legal division; the exact classical target \(1\) satisfies this condition.
No classical convergence assertion follows.

A primitive compressed cycle of length \(h\), with \(r\) affine instructions,
expands to a primitive raw cycle of length \(h+ar\). Every nonzero raw cycle
recovers at an affine phase, and zero has period one. Expansion induces a
bijection of periodic mutual-reachability classes, not a one-step conjugacy
or a bijection of periodic point sets at their original seeds. Signed raw
replay checks the bounded sample independently of the universal formal proofs.

### Common-base super-offset escape

[QCD.CommonBase.001](QCD.CommonBase.001/README.md) classifies every signed seed
for
\[
Q=t^u,\qquad D=t^v,\qquad C=t^a s,\qquad
t\ge2,\quad 0<u<v,\quad \gcd(u,v)=1,\quad a\ge u+v,\quad s\ne0.
\]
The base may be composite and the offset residual need not be a unit.
For a nonzero seed, a finite legal division prefix and a complete phase sweep
give the exact same-seed raw ray
\[
F^{r_0+j(u+v)}(n)
=x+j\,s\,t^{a-u-v+1+k}\sum_{i=0}^{v-1}t^i.
\]
Every nonzero signed seed escapes along the full raw sequence and eventually
has the offset's sign, with explicit magnitude and sign budgets. Zero is the
only periodic point. At the lower threshold, \((Q,C,D)=(2,4,4)\) has the
primitive positive raw cycle \(1,6,16,4\), refuting a uniform lowering by one.
The divisor here is positive; other offset regimes and negative divisors are
separate families.

### Gcd division barrier and affine escape

[QCD.AffineEscape.001](QCD.AffineEscape.001/README.md) classifies every positive
raw orbit when
\[
q\ge2,
\qquad c\ge1,
\qquad D\ge2,
\qquad \gcd(q,D)\nmid c.
\]
After the finite initial run that removes the largest whole-base power of
\(D\) from the seed, no further division is possible. If the remaining state
is \(x\), then the exact tail is
\[
q^j x+c\frac{q^j-1}{q-1},
\]
so every positive seed tends to infinity. The condition is sufficient rather
than necessary and supplies no conclusion for the classical cell.

### Multiplicatively independent homogeneous escape

[QCD.Homogeneous.001](QCD.Homogeneous.001/README.md) proves a positive escape
theorem for the homogeneous case \(c=0\) when \(q,D\ge2\) and
\[
q^a\ne D^b
\qquad\text{for all }a,b\ge1.
\]
Every positive raw orbit is injective and tends to infinity. A nonempty return
would force an equality \(q^A=D^E\) from its affine and division counts;
injectivity then upgrades to a full-sequence limit because each bounded set of
positive integers is finite. An exact factor-free power search decides whether
the independence hypothesis holds.

### Multiplicatively dependent homogeneous periodicity

[QCD.Homogeneous.002](QCD.Homogeneous.002/README.md) classifies the complementary
homogeneous case. If \(q^a=D^b\) for some positive \(a,b\), there is a
primitive presentation
\[
q=t^u,\qquad D=t^v,\qquad \gcd(u,v)=1.
\]
Writing a positive seed as \(rt^k\) with \(t\nmid r\) makes \(r\) invariant and
reduces the raw dynamics to
\[
k\longmapsto
\begin{cases}
k-v,&v\le k,\\
k+u,&k<v.
\end{cases}
\]
After a strictly decreasing transient, this is addition by \(u\) modulo
\(u+v\). Every positive orbit therefore enters a primitive raw cycle of length
\(u+v\), and every iterate is at most \(qDn\). Together with
`QCD.Homogeneous.001`, this is a complete positive homogeneous dichotomy for
\(q,D\ge2\).

### Unit-multiplier homogeneous fixed points

[QCD.Homogeneous.003](QCD.Homogeneous.003/README.md) classifies the boundary
case \(q=1\), \(c=0\), and \(D\ge2\). Every positive seed has a unique form
\[
n=rD^k,\qquad D\nmid r,
\]
and its exact raw orbit is
\[
T_D^j(n)=rD^{k-j},
\]
with truncated subtraction. Hence it first reaches \(r\) at time \(k\), then
remains fixed; the positive cycles are exactly the one-point cycles on
positive \(D\)-free integers. Every iterate is at most its seed. This supplies
the unit-multiplier boundary outside the \(q,D\ge2\) dichotomy.

### Additive access and finite cores

[QCD.Additive.001](QCD.Additive.001/README.md) treats \(q=1\), \(c\ge1\),
and \(D\ge2\). Put
\[
g=\gcd(c,D),\qquad L=D/g,\qquad
B=c(L-1),\qquad N=\left\lfloor\frac{B}{D-1}\right\rfloor.
\]
An inaccessible state \(g\nmid n\) has the exact escaping tail \(n+jc\).
Otherwise there is a unique \(0\le\ell<L\) with \(D\mid n+\ell c\);
its first-division endpoint is \((n+\ell c)/D\), reached in exactly
\(\ell+1\) raw instructions. These endpoints strictly decrease above \(N\)
and remain in the core when accessible below it. Every positive seed reaches
this finite core or an inaccessible state. With
\[
\delta(n)=(D-1)n-B,\qquad 1\le\varepsilon=\delta(N+1)\le D-1,
\]
the exact condition \(D^h\varepsilon>\delta(n)\) gives a raw entry bound
\(hL\). Coprime offsets have \(N=c\) and no traps; an empty core forces
full-sequence escape.

### Complete positive additive cycle classification

[QCD.Additive.002](QCD.Additive.002/README.md) classifies every positive raw
cycle for \(q=1\), \(c\ge1\), and \(D\ge2\). Extract
\[
c=st,\qquad \gcd(t,D)=1,\qquad s\mid D^k,
\qquad M=\left\lfloor\frac{t(D/\gcd(c,D)-1)}{D-1}\right\rfloor.
\]
The primitive cycles are exactly the full orbits of inverse multiplication by
\(D\) modulo \(t\) whose positive representatives all lie at most \(M\).
An edge \(m\to m'\) expands into \((Dm'-m)/t\) additions and one division
starting at \(sm\), preserving its least raw period. For modular period \(h\),
\[
h=\operatorname{ord}_{t/\gcd(m_0,t)}(D),\qquad
P=h+\frac{(D-1)\sum_{i<h}m_i}{t},\qquad h\le t\le c.
\]
Residue zero is represented by \(t\); modulus-one order is one. The window
prevents noncoprime scaling ghosts, and the raw clock is grouped before
division. Complete enumeration consumes at most \(t\) modular-state visits,
with preprocessing, big-integer arithmetic and expansion costs separate.

### Positive additive all-seed outcomes

[QCD.Additive.003](QCD.Additive.003/README.md) closes the positive all-seed
classification for exactly \(q=1\), \(c\ge1\), and \(D\ge2\). Every seed
is eventually periodic or reaches an inaccessible phase with an exact
escaping affine tail. In particular,
\[
\text{every positive seed is eventually periodic}
\quad\Longleftrightarrow\quad \gcd(c,D)=1.
\]
With the same core radius \(N\) and access length \(L\), a seed \(n\) has
an outcome phase at raw time \(u\le(n+N)L\), and a return witness has
\(0<p\le NL\). Escape is equivalent to a finite trap witness; universal
escape is equivalent to the absence of a positive raw cycle, decidable by
the complete whole-orbit test above. The bounded arbitrary-precision outcome
checker distinguishes resource refusal from certified periodicity or escape.

## Other map conventions

A residue-wise affine map has the form
\[
T(n)=\frac{q_r n+c_r}{d},\qquad r=n\bmod d,
\qquad c_r\equiv-q_r r\pmod d.
\]
A common multiplier is the special case \(q_r=q\).
This is a different map from raw branching. Shortcut, odd-accelerated and
first-division maps also have their own definitions and clocks.

## Build

`make` and `make lean` build the formal library. The `tex` profile uses pdfLaTeX
and BibTeX with `amsalpha`; the `go` profile uses `CGO_ENABLED=0`.

[Homomorphism theorem examples](Templates/lean/HomomorphismTheorems.lean) ·
[TeX example](Templates/tex/Template.tex) ·
[Go example](Templates/go/HomomorphismTheorems.go)

## License

[CC-BY-4.0](LICENSE.md).
