<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Foundations

[Detailed proofs](tex/Foundations.tex) · [Formal proofs](lean/GeneralizedCollatz.lean) ·
[Exact arithmetic](go/Dynamics.go) · [Arithmetic tests](go/Dynamics_test.go)

## Signed raw dynamics

Let \(q,c,d\in\mathbb Z\), \(|d|\ge2\), and
\[
F(n)=\begin{cases}n/d,&d\mid n,\\qn+c,&d\nmid n.\end{cases}
\]
An affine instruction is legal only when \(d\nmid n\); a division instruction
is legal only when \(d\mid n\).

**Theorem.** Every successful word of length \(k\) is the unique first \(k\)
raw branch choices and ends at \(F^k(n)\). Conversely, every finite raw orbit
has this legal word.

[Partial composition](lean/GuardedDynamics.lean) ·
[Itinerary recovery](lean/GuardedRecovery.lean)

## Affine words

For \(a_i(x)=(P_i x+B_i)/Q_i\), \(Q_i\ne0\), chronological composition is
\[
a_2\circ a_1=
\left(P_2P_1,\ P_2B_1+B_2Q_1,\ Q_2Q_1\right).
\]
For exponent letters \((qx+c)/d^a\) with \(d\ne0\), define
\[
B_{\varnothing}=0,\qquad B_{a::w}=q^{|w|}+d^a B_w,
\]
where \(|w|\) in the recursion is the length of the tail \(w\).
The word data are
\[
P=q^{|w|},\qquad Q=d^{\sum w},\qquad B_{\mathrm{full}}=cB_w.
\]
Expanding a word into one affine letter followed by \(a\) division letters for
each entry \(a\) gives the same presentation. Hence a legally closed raw
expansion satisfies \((Q-P)n=B_{\mathrm{full}}\).
A rational fixed point alone does not establish guard legality.

[Affine composition and closure](lean/AffineWords.lean)

## Conductor

For \(\Delta\ne0\), set
\[
\gamma=\frac{|\Delta|}{\gcd(|\Delta|,|b|)}.
\]
**Theorem.**
\[
\gamma\mid|c|
\quad\Longleftrightarrow\quad
\Delta\mid bc
\quad\Longleftrightarrow\quad
\exists n\in\mathbb Z:\Delta n=cb.
\]
The determinant-zero case is separate: closure requires the full offset to vanish.

[Conductor proof](lean/Conductors.lean)

## Categories and clocks

A labelled graph retains vertices, edges, labels, source and target maps.
A marked system consists of two graph morphisms \(\mathcal T\to\mathcal L\to\mathcal X\).
Componentwise composition gives category structures without injective-mark or
determinism assumptions.

If \(h\circ f=g\circ h\) and \(B(hx)\Rightarrow A(x)\), then capture of \(h(x)\)
in \(B\) transfers to capture of \(x\) in \(A\) at the same time.
For \(h(fx)=g^{\tau(x)}(hx)\), put
\[
T_0(x)=0,\qquad T_{n+1}(x)=T_n(x)+\tau(f^n x).
\]
Then \(h(f^n x)=g^{T_n(x)}(hx)\). Target preservation transfers forward capture;
\(\tau\ge1\) implies \(T_n\ge n\).

[Graph categories](lean/MarkedGraphs.lean) ·
[Capture transport](lean/DynamicalMorphisms.lean)

## Counterexamples

- \((q,c,d)=(2,2,-2)\): \(1\to4\to-2\to1\).
- \((3,5,2)\): \((3\cdot5+5)/4=5\); replacing the offset by one changes the fixed point.
- Exponent word \((0,0,3,4)\) fixes \(1\) rationally, but its second raw affine letter is illegal.
- For \((-5,31,-6)\), \(AAD\) closes at \(4\). Scaling state and offset by two preserves
  this word; scaling by three makes its first letter illegal.

[Formal counterexamples](lean/RecoveryControls.lean)
