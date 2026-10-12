<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Supported Offset Absorption

Let
\[
F(n)=\begin{cases}n/D,&D\mid n,\\Qn+C,&D\nmid n,\end{cases}
\qquad Q,C,D\in\mathbb Z,\quad |D|\ge2.
\]
Division retains the sign of \(D\) and has precedence, including at zero.
For a supplied integer factor \(S\), assume
\[
S\mid C,\qquad \gcd(|S|,|D|)=1,\qquad S\mid Q^k
\]
for some \(k\in\mathbb N\), and put \(G=F_{Q,C/S,D}\).
These hypotheses force \(S\ne0\). They do not require
\(\gcd(|C|,|D|)=1\) or \(C\mid Q^k\).

[Detailed proofs](tex/SupportedOffsetAbsorption.tex) ·
[Entry and recovery](lean/SupportedOffsetAbsorption.lean) ·
[Gcd construction](lean/SupportedOffsetFactor.lean) ·
[Constructed-factor recovery](lean/SupportedOffsetExtracted.lean) ·
[Raw-cycle controls](lean/SupportedOffsetControls.lean) ·
[Exact raw replay](go/SupportedOffsetAbsorption.go)

## QCD.Scaling.002.CommonRawTail — common entry and raw tail

Every signed seed \(n\) has one entry time \(t\) and one integer \(m\) with
\[
F^t(n)=Sm,\qquad
F^{t+r}(n)=S G^r(m)\quad\text{for every }r\in\mathbb N.
\]
At most \(k\) affine instructions occur before entry. This is an affine-event
bound, not a bound of \(k\) raw steps. The proof uses the well-founded rank
\((k,|n|)\): division preserves the prepared divisibility condition and
strictly decreases the second coordinate; an affine edge lowers the first.

## QCD.Scaling.002.PreparedEntry — prepared divisibility

The weaker prepared condition \(S\mid Q^k n\) suffices for that seed.
If every prime dividing \(|S|\) divides \(|Q|\), the explicit nonoptimal
witness \(S\mid Q^{|S|}\) supplies all-seed entry. Prime support refers to
\(Q\), not to \(D+1\).

## QCD.Scaling.002.TargetEquivalence — target recovery

For every target predicate \(P\subseteq\mathbb Z\),
\[
\bigl(\forall m\in\mathbb Z\ \exists r:\ P(SG^r(m))\bigr)
\quad\Longleftrightarrow\quad
\bigl(\forall n\in\mathbb Z\ \exists t:\ P(F^t(n))\bigr).
\]
No target-invariance assumption is needed. If \(S>0\), \(Q\ge0\),
\(C>0\), and \(D>0\), the same equivalence holds with both universal
quantifiers restricted to positive seeds. The common normalized entry state
is then positive, and \(C/S>0\).

This is not a pointwise equivalence between the same original and normalized
seed. Scaling is a raw-clock conjugacy on \(S\mathbb Z\), not on the whole
integer state space; different seeds can have different entry times.

## QCD.Scaling.002.CycleRecovery — cycles at the same raw clock

Every periodic original state already lies in \(S\mathbb Z\).
For every signed \(m\) and every raw time \(r\),
\[
F^r(Sm)=Sm\quad\Longleftrightarrow\quad G^r(m)=m.
\]
Consequently every original cycle recovers one core cycle, every phase is
scaled by \(S\), and its primitive raw period is unchanged. This assertion
uses all positive return times, not just one return witness.

## QCD.Scaling.002.SearchCutoff — exact starting cutoff

For \(S>0\) and natural starting cutoffs \(H,n\), the exact conversion is
\[
H\le Sn\quad\Longleftrightarrow\quad
\left\lfloor\frac{H+S-1}{S}\right\rfloor\le n.
\]
It includes \(H=0\). It converts a search cutoff; it does not itself
perform or exhaust a cycle search.

## QCD.Scaling.002.FactorExtraction — maximal supported factor

For \(C\ne0\), start with \(h=|C|\) and \(\Sigma=1\).
Repeatedly set
\[
g=\gcd(h,|Q|),\qquad
(\Sigma,h)\leftarrow(\Sigma g,h/g)
\]
until \(g=1\). Each nonterminal step has \(g\ge2\) and strictly lowers
\(h\). The result satisfies
\[
\Sigma h=|C|,\qquad \gcd(h,|Q|)=1,\qquad
\Sigma\mid Q^k\text{ for some }k\le|C|.
\]
For a positive divisor \(a\mid |C|\), all its prime factors divide
\(|Q|\) if and only if \(a\mid\Sigma\). Thus this is the maximal
supported factor in the divisibility order, including when \(Q=0\).
The core offset has magnitude \(h\), and neither factor exceeds \(|C|\).
The positive certificate excludes the constructor's separate zero-offset
fallback \((1,0)\).

## QCD.Scaling.002.ConstructedRecovery — one computed factor

Under the sufficient hypothesis \(\gcd(|C|,|D|)=1\), the computed factor
is automatically coprime to \(D\). It therefore supplies the common-tail,
target and cycle recovery above, and the core offset is coprime in magnitude
to the unchanged multiplier. If \(C>0\) and \(\Sigma>1\), the offset
strictly decreases. When \(\Sigma=1\), the offset was already coprime to
\(Q\), and no strict reduction is claimed.

For example, \((Q,C,D)=(11,55,2)\) gives \(\Sigma=11\), core offset
\(5\), and \(1\mapsto66=11\cdot6\). Entry into the whole offset lattice
would require a different hypothesis. The supplied factor \(S=3\) also
works for \((3,6,2)\), although \(\gcd(C,D)\ne1\); this case uses the
generic supplied-factor theorem, not the stronger automatic-extraction
admissibility criterion.

For \((181,181^{20},2)\), the core is \((181,1,2)\).
The odd-state pairs \((27,611)\) and \((35,99)\) have raw words
\(O D^3 O D^{12}\) and \(O D^6 O D^9\), respectively.
Both primitive raw periods are \(17\), and lifting multiplies every state
and the minima \(27,35\) by \(181^{20}\).

## Exact bounded replay

The Go program constructs and independently checks the factor's power
certificate, then checks entry, the affine budget and sixteen common raw
tail edges with both guards. Its fixed box uses \(-7\le Q\le7\),
\(1\le|C|\le32\), \(2\le|D|\le8\),
\(\gcd(|C|,|D|)=1\), and \(-64\le n\le64\).
It reports \(1{,}044{,}900\) seed/parameter certificates, not distinct orbits.

Additional tests cover supplied factors, signed divisors, zero multipliers,
502-bit signed seeds, both lifted raw cycles, exact ceiling boundaries and
invalid-input refusals. Zero allocations are measured only for four warmed
configurations with seed \(27\).

The replay accepts nonzero offsets and positive supplied factors; the
signed-factor and zero-offset entry theorems have wider domains.
The implementation bounds coefficients and supplied raw/core seeds to 512 bits,
restricts \(|Q|\le181\) and \(2\le|D|\le32\), and refuses a prefix exceeding
4096 raw steps. These are computational limits, not hypotheses of the formal
theorems. Refusal is not nonabsorption, divergence or search exhaustion.

## Commands

The construction extends [QCD.Scaling.001](../QCD.Scaling.001/README.md).

```sh
make lean
make go GOFILE=QCD.Scaling.002/go/SupportedOffsetAbsorption.go
make tex TEXFILE=QCD.Scaling.002/tex/SupportedOffsetAbsorption.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
