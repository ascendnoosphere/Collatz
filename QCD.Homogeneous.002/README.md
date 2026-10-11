<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# QCD.Homogeneous.002 — Dependent homogeneous periodicity

This result classifies the positive homogeneous raw map when its two
coefficients are multiplicatively dependent. Let

\[
T_{q,D}(n)=
\begin{cases}
n/D,&D\mid n,\\
qn,&D\nmid n,
\end{cases}
\qquad q,D\ge 2,
\]

on positive integers. If \(q^a=D^b\) for positive \(a,b\), then every orbit is
eventually periodic. The proof gives the primitive period and a uniform
source-relative height bound.

## QCD.Homogeneous.002.1 — Primitive common-base normal form

There are integers

\[
t\ge 2,\qquad u,v\ge 1,\qquad \gcd(u,v)=1
\]

such that

\[
q=t^u,\qquad D=t^v.
\]

Starting from \(q^a=D^b\), divide \(a,b\) by their gcd and compare prime
factorizations. Coprimality forces every exponent vector to be a multiple of
the same primitive vector.

## QCD.Homogeneous.002.2 — Exponent dynamics

Write each positive state uniquely as

\[
n=r t^k,\qquad t\nmid r.
\]

The factor \(r\) is invariant. The exponent follows

\[
F(k)=
\begin{cases}
k-v,&v\le k,\\
k+u,&k<v.
\end{cases}
\]

Every exponent reaches the interval \(0\le k<u+v\). Inside that interval,

\[
F(k)\equiv k+u\pmod{u+v}.
\]

Since \(\gcd(u,u+v)=1\), this rotation has one orbit and primitive period
\(u+v\).

## QCD.Homogeneous.002.3 — Exact raw reconstruction

For a positive seed \(n\), let

\[
k_0=\max\{e:t^e\mid n\},\qquad r=n/t^{k_0}.
\]

At every raw time \(j\),

\[
T_{q,D}^{j}(n)=r t^{F^j(k_0)}.
\]

Thus every positive orbit enters a primitive raw cycle of length \(u+v\).
No shorter positive return is possible on the periodic tail. The natural-state
map is also proved to be exactly the positive restriction of the foundational
signed raw map.

## QCD.Homogeneous.002.4 — Height bound

Every raw iterate satisfies

\[
T_{q,D}^{j}(n)\le qDn.
\]

Indeed, every exponent iterate is below
\(\max\{k_0+1,u+v\}\), hence at most \(k_0+u+v\). Multiplying by the invariant
factor gives

\[
r t^{F^j(k_0)}\le r t^{k_0+u+v}=qDn.
\]

## Certified reduction

- **Original obligation:** classify every positive orbit for \(c=0\),
  \(q,D\ge2\), under the stated multiplicative dependence.
- **Replacement obligations:** extract the primitive common base, solve the
  exponent recurrence, and reconstruct every integer state.
- **Recovery:** the invariant factor and exponent formula reconstruct each raw
  state at the same raw time; no clock is changed.
- **Strict decrease:** while an exponent is outside the recurrent interval,
  one update subtracts the positive quantity \(v\). The process therefore
  terminates in a finite set of \(u+v\) exponents, where the coprime rotation is
  solved exactly.
- **Preservation conditions:** positive seeds, \(q,D\ge2\), zero offset, and
  positive exponents in the dependence relation.

Together with `QCD.Homogeneous.001`, this settles the positive homogeneous
case for \(q,D\ge2\): independent coefficients escape, while dependent
coefficients are eventually periodic.

## Checked artifacts

- `lean/DependentHomogeneous.lean` proves the common-base normal form, exact
  exponent recurrence, raw reconstruction, primitive tail period, height
  bound, and positive raw-map bridge.
- `go/DependentHomogeneous.go` constructs arbitrary-precision transient,
  cycle, and height certificates.
- `go/DependentHomogeneous_test.go` checks composite bases, exact exponent
  rotation, primitive return, coefficient dependence, in-place stepping,
  ownership, tamper rejection, validation failures, and an exhaustive bounded
  family.
- `tex/DependentHomogeneous.tex` gives the detailed mathematical proof and
  scope boundary.

The result does not address nonzero offsets, zero seeds, negative seeds, or
signed divisors. It makes no claim about universal classical Collatz capture.
