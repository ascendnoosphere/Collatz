<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Complex Collatz maps: conventions and related literature

A complex extension must specify both its integral state space and its
division rule. Equal norms or matching cycle values do not identify
two dynamical systems.

## Integral and residue-wise maps

The raw rule on an integral quadratic order divides by an element only
when the quotient remains in that order. For Gaussian coordinates,

```math
2\mid x+iy\iff 2\mid x\ \text{and}\ 2\mid y,\qquad
1+i\mid x+iy\iff x\equiv y\pmod2.
```

The first quotient has four residue classes; the second has two.
Their guards and branch alphabets cannot be exchanged.

The four-residue Joseph convention instead uses
$`r=(x\bmod2)+(y\bmod2)i`$ and

```math
J_+(z)=\begin{cases}z/2,&r=0,\\(3z+r)/2,&r\ne0.\end{cases}
```

[Kucinski00] studies this Gaussian convention. The minus version and
Eisenstein-coordinate versions in this library are specified separately.
Nonreal cycles of $`J_+`$ do not contradict raw scalar off-axis escape:
the maps have different affine instructions.

[Kionke17] develops geometric methods for higher-dimensional integral
Collatz mappings. The scalar lattice results here use exact transverse
multiplicative identities and content instead of importing a cone-density
theorem. Equal norms are not enough: the Gaussian pair
$`q=2+i,d=2-i`$ satisfies $`-q+(1+i)d=1`$ and has independent powers,
yielding [homogeneous escape](../QCD.GaussianDynamics.001/README.md).

## Fields and cochains

Literal field divisibility collapses a raw rule: for $`d\ne0`$, every
$`z`$ is $`d(z/d)`$. The affine permutations of finite quadratic fields
in this library are deliberately defined models, not quotients of raw
lattice division.

Finite graph cohomology and twisted affine transport retain different data.
Ordinary $`H^1`$ counts weak components of a finite functional graph.
Twisted transport retains ordered edge multipliers and offsets.
[Cycle arithmetic](../QCD.ComplexCohomology.001/CycleArithmetic.md) proves
integral recovery under its coprimality hypotheses; a field solution alone
does not supply that recovery or a legal itinerary.

## Holomorphic interpolation

[Chamberland96] studies a continuous real extension of the classical
shortcut. [AnalyticClaims.md](AnalyticClaims.md) gives its integer-value and
derivative calculations, and an entire perturbation preserving every
integer value while changing derivatives at finitely many integers.

The polynomial portraits here serve a related but narrower purpose:
four declared polynomials preserve selected raw cycle nodes while giving
different multipliers. The exact radius-eight growth estimate is proved
for those four polynomials. Numerical escape-time portraits are not a
classification of raw integer or lattice orbits.

## References

- **[Kucinski00]** Gina I. Kucinski, *Cycles for the 3x+1 Map on the Gaussian
  Integers*, May 2000 preprint.
  [Paper](https://monks.scranton.edu/files/pubs/kucinski.pdf).
  Its cycle enumeration concerns $`J_+`$; no exhaustive enumeration theorem
  from that paper is assumed by the raw lattice proofs.
- **[Kionke17]** Steffen Kionke, *A Geometric Approach to Divergent Points of
  Higher Dimensional Collatz Mappings*, *Monatshefte für Mathematik* 182
  (2017), 851–863.
  [DOI](https://doi.org/10.1007/s00605-016-0947-4) ·
  [arXiv:1511.05893](https://arxiv.org/abs/1511.05893).
- **[Chamberland96]** Marc Chamberland, *A Continuous Extension of the 3x+1
  Problem to the Real Line*, *Dynamics of Continuous, Discrete and Impulsive
  Systems* 2 (1996), 495–509.
  [Paper](https://chamberland.math.grinnell.edu/papers/3x_1996.pdf).

BibTeX entries are in [ComplexDynamics.bib](tex/ComplexDynamics.bib).
The independent local corpus is indexed in
[Library.SourceCatalogue.001](../Library.SourceCatalogue.001/README.md).
