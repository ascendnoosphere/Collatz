<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Mixed-radix descent covers of the residual

Status: **REFUTED ROUTE** for finite covers by uniform direct-descent
cylinders. The argument allows arbitrary odd factors in the source moduli.
It does not exclude smaller-parent joins or unbounded-depth constructions.

Throughout, $`T(n)=n/2`$ for even inputs and $`T(n)=(3n+1)/2`$ for odd inputs.
The residual $`\mathcal R_{\mathrm E}`$ is defined in the
[ClassicalCoalescence article](../../QCD.ClassicalCoalescence.001/README.md).

## Exact cylinder and descent conditions

For a word of length $`h`$ with $`r`$ odd letters, write
$`F_w(x)=(3^rx+B_w)/2^h`$. Starting at $`B_0=0`$, an even letter leaves
$`B_j`$ unchanged and an odd letter gives $`B_{j+1}=3B_j+2^j`$.

Let $`M=2^km`$ with $`m`$ positive and odd. If the word is legal at $`a`$
and $`k\ge h`$, then for every nonnegative integer $`t`$,

```math
T^h(a+Mt)=p_0+Nt,\qquad
p_0=T^h(a),\qquad N=3^rM/2^h.
```

Indeed, after $`j<h`$ ticks the increment from the base orbit is
$`3^{r_j}Mt/2^j`$, which is even. This preserves the next parity and proves
the identity by induction. Conversely, an integer endpoint slope requires
$`2^h\mid M`$, since $`3^r`$ is odd. The modulus action for
$`M=2^k3^j`$ is therefore $`(k,j)\mapsto(k-h,j+r)`$.

Assume $`a\ge1`$ and $`h\ge1`$. The cylinder is a strict descent at every
$`t\ge0`$ exactly when

```math
0<p_0<a\quad\text{and}\quad 3^r<2^h.
```

Positivity follows from the positive base orbit and nonnegative slope.
For the upper inequality, subtract $`a+Mt`$: its constant is $`p_0-a`$
and its slope is $`N-M`$. Both must be nonpositive, with the constant
strictly negative. Equality $`N=M`$ would require $`3^r=2^h`$, impossible
for $`h\ge1`$. Thus the stated conditions are necessary and sufficient.
An odd modulus factor changes boundary representatives but does not repair
a slope with $`3^r\ge2^h`$.

## Residual points near the all-odd itinerary

Put $`C_k=\{n\ge1:n\equiv-1\pmod{2^k}\}`$. For $`k\ge13`$,

```math
\mathrm d(\mathcal R_{\mathrm E}\cap C_k)=\frac{22}{81}\,2^{-k}>0.
```

To compute this density, separate the exact valuations
$`a=v_2(n+1)\ge k`$ and write $`n=2^au-1`$ with $`u`$ odd. At these
valuations, the second-burst and paired-tail families cannot occur, and all
later direct-cylinder exclusions have incompatible residues modulo $`8192`$.
The remaining guards are

```math
3\nmid u,\qquad 3^au\equiv3\pmod4,\qquad
n\not\equiv4\pmod9,\qquad n\not\equiv10\pmod{81}.
```

The mod-four guard selects one odd class modulo four. Modulo 81, the three
forbidden sets have sizes 27, 9, and 1. The latter two lie in different
classes modulo nine, and both require $`u\not\equiv0\pmod3`$, so all
three are disjoint. The Chinese remainder theorem leaves 44 classes modulo
$`4\cdot81`$. At exact valuation $`a`$, their density in $`n`$ is
$`44/(324\cdot2^a)`$. Summing gives

```math
\sum_{a=k}^{\infty}\frac{44}{324\cdot2^a}
=\frac{22}{81}\,2^{-k}.
```

This sum computes a natural density: after truncating at $`a<L`$, the
omitted set is contained in $`C_L`$, whose density is $`2^{-L}`$.
This tail bound justifies passing to the infinite sum. For smaller $`k`$,
infinitude follows from $`C_{13}\subseteq C_k`$.

## No finite direct-descent cylinder cover

Suppose a finite family of legal uniform cylinders covers
$`\mathcal R_{\mathrm E}\cap C_k`$, and each certificate supplies a strict
descent after its fixed word length $`h_i\ge1`$. Choose
$`K\ge\max\{k,13,h_1,\ldots,h_s\}`$. The preceding density calculation
supplies a positive $`n\in\mathcal R_{\mathrm E}\cap C_K`$.

Its first $`K`$ inputs are odd: for $`0\le j\le K`$,
$`T^j(n)+1=3^j(n+1)/2^j`$. At each of the first $`K`$ ticks,
$`T(x)=(3x+1)/2>x`$. Thus $`T^{h_i}(n)>n`$ for every certificate in the
family, contradicting coverage. This proof uses only the finite word lengths;
adding odd factors 3, 5, or 7 to the moduli cannot evade it.

The remaining sufficient condition is a smaller-parent theorem for every
residual seed, with the parent positive and strictly smaller. The obstruction
above rules out one fixed finite direct-descent cover. It does not require
all successful parent methods to have one particular form or parameter.

## Historical experiments

The original workstream recorded dyadic enumeration through depth 22 and
mixed-radix enumeration through binary depth 18 and ternary depth 6 in
`/tmp/opencode/Agent10/MixedRadixCover.go`. That temporary program is not
retained here, so its large tables are not included as reproducible certificates.
The proofs above do not depend on them. In particular, unweighted counts of
residue classes meeting the residual do not bound the fraction of residual
integers covered unless their class weights are also proved.
