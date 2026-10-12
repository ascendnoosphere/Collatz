<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Congruence transport of affine states

Let \(q,c,n,t,d\) be integers and let \(j\) be a natural number. Write
\(T_0(q)=0\) and \(T_{j+1}(q)=T_j(q)+q^j\), and define the affine state
\[
A_j(q,c,n)=q^j n+c\,T_j(q).
\]
A parameter record \(p\) consists of a multiplier \(q\), an offset \(c\), and
a divisor \(d\) with \(|d|\ge 2\). The time \(j\) is a first hit of the seed
\(n\), written \(\operatorname{Hit}(p,n,j)\), when \(d\) divides
\(A_j(q,c,n)\) and \(d\) divides \(A_i(q,c,n)\) for no natural number \(i<j\).

For every \(q,c,n,t,d\in\mathbb{Z}\) and every \(j\in\mathbb{N}\),
\[
A_j(q,c,n+td)=A_j(q,c,n)+q^j td.
\]
The difference at that time is \(q^j td\), hence is a multiple of \(d\). The
same holds at every earlier time, because the identity does not restrict
\(j\). Consequently, for a parameter record with divisor \(d\), and for every
time \(i\),
\[
d\mid A_i(q,c,n)\quad\text{if and only if}\quad d\mid A_i(q,c,n+td).
\]
Both directions use an explicit integer witness: if the unshifted state is
\(dm\) and the difference is \(dk\), the shifted state is \(d(m+k)\); if the
shifted state is \(dm\), the unshifted state is \(d(m-k)\). Therefore, for
every integer shift \(t\) and every time \(j\),
\[
\operatorname{Hit}(p,n,j)\quad\text{if and only if}\quad
\operatorname{Hit}(p,n+td,j).
\]
The failure clause is included. Divisibility is compared at \(j\) and at
every \(i<j\), and each comparison is an equivalence.

## Reduction record

**ORIGINAL OBLIGATION.** For the affine state of a signed parameter record,
determine the effect of replacing the seed \(n\) by \(n+td\) on divisibility
by the record's divisor, at the prospective first-hit time and at every
earlier time, in both directions.

**REPLACEMENT OBLIGATIONS.** Prove the integer identity
\(A_j(q,c,n+td)=A_j(q,c,n)+q^j td\) for every integer \(q,c,n,t,d\) and every
natural number \(j\). Deduce that the difference is a multiple of \(d\) at
every time. Deduce the equivalence of divisibility at every time. Transport
both the divisibility at time \(j\) and the failures at all earlier times.

**RECOVERY ARGUMENT.** The identity is an equality in \(\mathbb{Z}\).
Specializing the free integer \(d\) to the divisor of the original parameter
record restores the original affine state and the original first-hit
predicate. No time is dropped: the difference at each \(i<j\) is a multiple
of \(d\), so the universal quantifier over earlier times survives in both
directions. The raw seed and the raw clock are not replaced by residue
representatives.

**DIFFICULTY DECREASE.** The unresolved comparisons are indexed by the time
\(i\in\mathbb{N}\). One application of distributivity removes that entire
family: after the identity, no time-indexed divisibility comparison remains
open. The decreasing resource is the number of open comparisons, which falls
from a family indexed by \(\mathbb{N}\) to zero. There is no residual child
indexed by time, and the proof does not recurse on \(j\).

**PRESERVATION CONDITIONS.** The algebraic identity quantifies over all
integers \(q,c,n,t,d\) and all natural numbers \(j\), with no positivity,
coprimality, or size restriction. The first-hit statement keeps the original
admissible divisor, namely an integer \(d\) with \(|d|\ge 2\), and quantifies
over every integer seed, every integer shift, and every time. Both directions
are proved. The predicate remains divisibility of the affine state, not a
statement about raw iterates.

## What is not claimed

- The identity does not assert that a first hit exists for any seed.
- The correction \(q^j td\) need not be nonzero, and the transport does not
  force \(|A_j(q,c,n)|\) to exceed any prescribed bound. It does not produce
  a large state.
- Equality of a raw iterate with the affine state is not proved. That
  equality needs a division-free prefix and is not a consequence of the shift.
- No return map, core bound, trap classification, density, or classical
  convergence statement is proved.
- Agreement of the difference identity on a finite set of integers is not a
  proof for every integer. The proof is the identity above.
