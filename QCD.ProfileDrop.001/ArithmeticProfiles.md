<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Arithmetic profiles of integers and pairs

A profile is a collection of partial arithmetic or representation observables.
This registry includes shared parameters, single-state properties and pair
relations, retaining repeated entries and their domain restrictions.
A well-defined observable is not automatically a dynamical invariant;
each row states its mathematical role or the additional data it requires.

Use $`q,c,d`$ for raw parameters, $`B`$ for a digit base, $`a,b`$ for pair
arguments, and $`\mathcal D`$ for a digit alphabet. This removes the schema's
collisions between the integer $`b`$ and the base, and between a divisor and
a digit set. Finite searches return **unknown outside the searched range**,
not the negation of an existential property.

## Domains and mathematical roles

- **Used:** an exact role in a proved mechanism, with links in the mechanism index.
- **Static:** well-defined arithmetic or representation data once its domain is fixed;
  no new orbit theorem is asserted.
- **Candidate:** a concrete possible use with an unproved dynamical bridge.
- **Specify:** the schema needs additional choices or a corrected definition.

Rows concerning primes, divisor sums, ordinary digits and classical named
integer classes use positive integers unless a signed extension is stated.
Factorization and prime support of a nonzero signed integer mean those of its
absolute value. Zero has no finite prime factorization and infinitely many
positive divisors; set $`v_p(0)=+\infty`$, not zero. A division by zero,
logarithm outside its real domain, or floating-point overflow is not a valid
profile value. Duplicate rows inherit the same restrictions.

The phrase "complete property set" is not a finite computable contract:
"etc.", an unspecified associated function, and unrestricted representations
are not enumerated predicates. The schema should be a registry of partial,
parameterized observables with explicit domains and certificate types.

## Division consumes residue precision

For **every** $`q,c\in\mathbb Z`$, $`d\ge2`$ and $`k\ge0`$, let
$`M=d^{k+1}`$. Division precedence gives

```math
0\equiv M\pmod M,\qquad T(0)=0,\qquad T(M)=d^k\not\equiv0\pmod M.
```

Thus no deterministic map on this fixed residue precision can recover every
raw successor. This refutes a memoryless $`d`$-adic profile quotient at any
fixed positive precision, **not** every conceivable finite factor or a
marked path construction. The lost datum is an additional division digit.
If divisible $`u,v`$ agree modulo $`d^{k+1}`$, their exact quotients do agree
modulo $`d^k`$: divide the identity $`u-v=d^{k+1}t`$ by $`d`$.

The complete formal statements are `RawPrecisionWitness`,
`NoFixedRawPrecision` and `DivisionPrecisionTransfer` in
[ProfilePrecision.lean](lean/ProfilePrecision.lean). They require no
expansion hypothesis on $`q`$, no coprimality, and no conjecture about hitting
times. [ProfileDrop.tex](tex/ProfileDrop.tex) contains the matching proof.

The witness excludes every successor function at the stated fixed precision.
Division instead transfers one higher precision to one lower precision.
Recovery through arbitrarily many divisions must retain additional data
or have a separately proved precision budget.

A complementary arithmetic invariant is the
[prime-exponent escape certificate](../QCD.ComplexLattice.001/README.md#general-scalar-escape-by-arithmetic-independence).
The common prime support of 12 and 18 does not detect independence; the two
exponent rows have minor three. In contrast, 4 and 8 have the same support and
are dependent, with a primitive nonreal five-cycle. Factor exponents, not just
radicals or support sets, supply the separating invariant.

## Mechanism index

| Mechanism | Proved role; retained limitation |
|---|---|
| [Residue and displacement](README.md) | Exact affine normal form and a finite zero-avoiding-cycle test for division-free escape; no global raw residue quotient. |
| [Prime-power arithmetic](lean/ProfilePrimePower.lean) | Restricted affine return/LTE lemmas with prime, parity and valuation hypotheses; not arbitrary signed hitting-time classification. |
| [Supported offset scaling](../QCD.Scaling.002/README.md) | Exact lattice, guard and cycle recovery for supported offsets; not arbitrary multiplication of seeds. |
| [Signed core](../QCD.SignedCore.001/README.md) | A proved uniform contraction inequality gives finite core entry; boundedness is not inferred from a profile label. |
| [Clock-aware word algebra](../QCD.Relations.Cycles.001/README.md) | Affine triples and legal words retain joint guards and clocks; integrality alone is insufficient. |
| [Complex scalar transfer](../QCD.ComplexLattice.001/README.md) | Full off-axis escape and order-to-order dynamical conjugacy; not a ring isomorphism or a solution on the integer axis. |
| [Quadratic arithmetic](../QCD.QuadraticArithmetic.001/README.md) | Norms, adjugate divisibility, ideals and bounded certificates; the README distinguishes written uniform results from their partial formal scope. |
| [Finite-field cochains](../QCD.ComplexCohomology.001/README.md) | Incidence ranks, holonomy and genuine quotients with specified coefficient fields; not reduction of raw division modulo a field. |

## Shared hyperparameters — 12 rows

| ID | Item | Assessment |
|---|---|---|
| H01 | n | Used: the actual signed state; a profile must retain its admissible domain. |
| H02 | a, b | Used: simultaneous pair witnesses, not two separately chosen states. |
| H03 | base b | Specify: rename B; ordinary positional digits require an integer base at least two. |
| H04 | prime p | Used: require primality before valuations, Legendre symbols or prime-power lifting. |
| H05 | modulus m | Used: take a positive modulus; distinguish affine residues from raw successors. |
| H06 | precision k | Used: a nonnegative integer; legal division consumes precision as proved above. |
| H07 | digit alphabet D | Specify: rename the alphabet; give completeness and uniqueness of the representation. |
| H08 | representation R | Specify: define encoding, decoding, domain and all tie-breaking rules. |
| H09 | sequence S | Specify: give a formula/recurrence, index domain and membership certificate. |
| H10 | number of powers N | Specify: nonnegative count, allowed signs and exponent; these are different parameters. |
| H11 | pseudoprime base a_p | Static: specify the base and whether coprimality is required by the chosen test. |
| H12 | search limit L | Used: a finite budget; failure to find a witness is only bounded nonexistence. |

## Profile A — core integer properties, 23 rows

| ID | Item | Assessment |
|---|---|---|
| A01 | sign | Used: signed traps and reflection; changing divisor sign changes the map. |
| A02 | parity | Used: exact binary guard, not a complete state description. |
| A03 | absolute value | Used: core contraction and discrete transverse escape; not always monotone. |
| A04 | factorization | Used: prime-exponent minors and offset support; zero is excluded. |
| A05 | divisors | Used: exact branch tests; the finite list requires a nonzero input. |
| A06 | proper divisors | Static: positive input and exclusion of the input itself. |
| A07 | aliquot sum | Static: positive input; no proved QCD transport from this different map. |
| A08 | gcd with hyperparameters | Used: accessibility, conductors and coprimality hypotheses. |
| A09 | perfect | Static: an aliquot fixed-point label, not a raw-QCD fixed-point criterion. |
| A10 | abundant | Static: compares the positive input with its aliquot sum. |
| A11 | deficient | Static: same positive-domain comparison; no monotone QCD invariant established. |
| A12 | semiperfect | Static: finite subset-sum certificate from proper divisors. |
| A13 | weird | Static: abundance plus failure of the complete finite subset-sum test. |
| A14 | practical | Static: distinct-divisor subset sums through the input; not arbitrary repeated sums. |
| A15 | amicable | Static: a common second input must satisfy both aliquot equations. |
| A16 | sociable | Static: a full aliquot cycle certificate with primitive length at least three. |
| A17 | untouchable | Candidate: a bounded preimage search cannot certify unrestricted untouchability. |
| A18 | squarefree | Used: support/radical summaries; they discard the exponent data needed for resonance. |
| A19 | powerful | Static: each occurring prime exponent is at least two; not the same as perfect power. |
| A20 | perfect power | Used: common-base homogeneous families; specify positive exponent and signed convention. |
| A21 | prime power | Used: restricted lifting arguments and single-prime models. |
| A22 | semiprime | Static: exactly two prime factors with multiplicity. |
| A23 | sphenic | Static: exactly three distinct prime factors, each exponent one. |

## Profile B — prime-related properties, 15 rows

| ID | Item | Assessment |
|---|---|---|
| B01 | prime | Used: prime divisibility and finite-field characteristics, not a seed escape criterion. |
| B02 | composite | Static: positive input greater than one, not prime. |
| B03 | twin prime | Static: specify whether either or both distance-two neighbors must be prime. |
| B04 | cousin prime | Static: same directional choice at distance four. |
| B05 | sexy prime | Static: same directional choice at distance six. |
| B06 | Mersenne prime | Static: primality of the displayed power-minus-one integer. |
| B07 | Fermat prime | Static: nonnegative exponent index; primality is a separate obligation. |
| B08 | Sophie Germain prime | Static: jointly check the input and twice it plus one. |
| B09 | safe prime | Static: odd prime input and primality of its half-predecessor. |
| B10 | emirp | Static: base-dependent reversal, different from the original prime. |
| B11 | palindromic prime | Static: base and leading-zero convention are required. |
| B12 | circular prime | Static: all chosen rotations, with fixed width and a leading-zero rule. |
| B13 | permutable prime | Static: all digit permutations; finite but larger than the rotation test. |
| B14 | Carmichael number | Static: composite positive input and all unit-base congruences. |
| B15 | pseudoprime base a | Static: one base is not the all-base Carmichael condition. |

## Profile C — figurate and sequence properties, 13 rows

| ID | Item | Assessment |
|---|---|---|
| C01 | triangular | Static: an integral nonnegative index witness; no raw closure inferred. |
| C02 | square | Used: quadratic coordinates/norms; a square seed need not stay square. |
| C03 | pentagonal | Static: specify ordinary versus generalized integer-index convention. |
| C04 | hexagonal | Static: nonnegative index and exact formula. |
| C05 | etc. | Specify: an open-ended family is not one test; supply each polygonal formula. |
| C06 | Fibonacci | Static: state the indexing and whether signed indices are allowed. |
| C07 | Lucas | Static: fix initial values and indexing. |
| C08 | factorial | Static: nonnegative factorial index; 0 and 1 have the same factorial value. |
| C09 | Catalan | Static: nonnegative index and exact integer formula. |
| C10 | repunit | Used: geometric sums in the repunit-cycle construction, with a fixed base. |
| C11 | sum of two squares | Used: Gaussian norms and exact two-coordinate witnesses. |
| C12 | sum of N squares | Candidate: specify integer summands; representation does not preserve the raw guard automatically. |
| C13 | Waring-type | Specify: exponent, number of summands, signs and exact versus bounded existence. |

## Profile D — base representation properties, 17 rows

| ID | Item | Assessment |
|---|---|---|
| D01 | representation string | Used: a reversible encoding; retain the sign and leading-zero convention. |
| D02 | number of digits | Static: a coarse height; zero needs a convention. |
| D03 | digit sum | Candidate: gives congruence modulo base minus one, not a complete division profile. |
| D04 | digit product | Static: discards position and can vanish for nonzero inputs. |
| D05 | palindrome | Static: base-dependent symmetry, not symmetry of the raw map. |
| D06 | repdigit | Static: fixed digit and width; excluding leading zero matters. |
| D07 | repunit | Used: same geometric-sum mechanism as C10. |
| D08 | Harshad/Niven | Static: positive digit sum must divide the positive input. |
| D09 | Armstrong/narcissistic | Static: digit count supplies the exponent; not a dynamical invariant. |
| D10 | automorphic | Static: congruence modulo the base raised to the chosen width. |
| D11 | Kaprekar | Specify: width, allowed zero pieces and split position. |
| D12 | Smith | Static: composite input and factor digits counted with multiplicity. |
| D13 | happy/sad | Static: a different digit-square map; prove a finite trap before asserting search termination. |
| D14 | self number | Candidate: specify base; a finite generator bound is needed for a complete negative test. |
| D15 | factorion | Static: fixed-base sum of digit factorials. |
| D16 | Friedman | Specify: allowed operations, parentheses, reuse and exclusion of trivial expressions. |
| D17 | expansion of 1/n | Used: termination means every prime divisor of the reduced denominator divides the base; n is nonzero. |

## Profile E — modular properties, 8 rows

| ID | Item | Assessment |
|---|---|---|
| E01 | n mod m | Used: exact affine residue and first-access data; not a global raw quotient. |
| E02 | congruence class | Used: quotient equality; division may require one higher precision. |
| E03 | modular inverse | Used: only units have inverses; check gcd one. |
| E04 | order modulo m | Used: unit order in access arithmetic; do not replace an affine period by multiplier order. |
| E05 | quadratic residue/nonresidue | Static: exact square witnesses; composite moduli need their own convention. |
| E06 | primitive root | Static: the unit group need not be cyclic; existence is not automatic. |
| E07 | CRT representation | Used: pairwise-coprime moduli give reversible residue data modulo their product. |
| E08 | residue number system | Used: bound the integer decoding range; without it the data specify only a congruence class. |

## Profile F — p-adic properties, 7 rows

| ID | Item | Assessment |
|---|---|---|
| F01 | valuation | Used: dyadic descent and coefficient exponent minors; infinity at zero. |
| F02 | p-adic norm | Used: exact valuation reformulation; not an Archimedean escape estimate by itself. |
| F03 | p-adic unit | Used: valuation zero, supporting inverse/LTE hypotheses. |
| F04 | p-adic integer | Static: every ordinary integer has this property, so it separates no integer seeds. |
| F05 | expansion modulo p^k | Used: finite precision; raw division loses digits as proved above. |
| F06 | p-adic power | Candidate: finite congruence witnesses alone do not prove an infinite compatible root. |
| F07 | Legendre factorial formula | Static: exact factorial valuation; no QCD return bridge is asserted. |

## Profile G — other representations, 17 rows

| ID | Item | Assessment |
|---|---|---|
| G01 | negative bases | Static: specify base, alphabet and finite decoding convention. |
| G02 | complex bases | Specify: base, digit set, existence and uniqueness; not every complex base is a numeration system. |
| G03 | balanced ternary | Static: reversible signed-integer encoding with the specified three digits. |
| G04 | bijective numeration | Static: positive domain and alphabet without zero. |
| G05 | Roman numerals | Specify: range, canonical syntax and extension to zero/negative values. |
| G06 | Egyptian fractions | Specify: nonzero denominator and signs; an integer does not select a unique expansion. |
| G07 | continued fractions | Static: an integer's canonical simple continued fraction is its one-term value. |
| G08 | Zeckendorf | Static: positive domain, Fibonacci indexing and nonadjacent summands. |
| G09 | factoradic | Static: nonnegative domain and mixed-radix digits. |
| G10 | primorial base | Specify: the exact ordered mixed radices and digit bounds. |
| G11 | Gray code | Static: fix width or nonnegative domain; adjacency is not raw-QCD adjacency. |
| G12 | two's complement | Used: machine boundary tests; a fixed width represents only a bounded signed range. |
| G13 | IEEE 754 | Used: distinguish floating portraits from exact certificates; integer rounding is lossy. |
| G14 | Elias gamma/delta | Static: positive-domain prefix encoding; code length is not an orbit potential. |
| G15 | run-length encoding | Static: specify the underlying canonical string and delimiters. |
| G16 | permutation rank/Lehmer code | Specify: permutation size and indexing; arbitrary integers need a size-dependent range. |
| G17 | partitions/compositions | Static: positive summands and finite input; ordered and unordered families differ. |

## Profile H — analytic/geometric/combinatorial, 7 rows

| ID | Item | Assessment |
|---|---|---|
| P.H01 | Taylor/Laurent series | Specify: an associated function, center, domain and convergence or formal-series category. |
| P.H02 | Fourier coefficients | Specify: function/measure, group, normalization and coefficient field. |
| P.H03 | Dirichlet series | Specify: an entire coefficient sequence and convergence domain, not one integer label. |
| P.H04 | polygonal/centered polygonal | Static: specify the polygon count and centered versus ordinary formula. |
| P.H05 | polyhedral numbers | Specify: the geometric family and exact counting convention. |
| P.H06 | lattice-point representations | Used: exact quadratic coordinates and norm forms; embeddings retain multiplicity. |
| P.H07 | graph/matroid/poset | Used: finite orbit graphs and incidence operators; an arbitrary encoding needs recovery and admissibility proofs. |

## PairProfile 1 — order/equality/sign/parity, 8 rows

| ID | Item | Assessment |
|---|---|---|
| 1.01 | equality/inequality | Used: exact collision certificates and their negations. |
| 1.02 | order relations | Used: well-founded positive descent; signed magnitude is a different order. |
| 1.03 | same/opposite signs | Used: reflection and sign-alternating families, with zero handled separately. |
| 1.04 | positive/negative/zero pair | Used: exhaustive signed boundary cases. |
| 1.05 | same/opposite parity | Used: binary congruence and phase rigidity; specify simultaneous adjacent phases. |
| 1.06 | absolute distance | Used: integral separation and error bounds; not a contraction without an estimate. |
| 1.07 | midpoint | Static: generally rational, integral exactly for equal parity. |
| 1.08 | ratio | Used: scaling maps on their legal domains; denominator nonzero. |

## PairProfile 2 — arithmetic operations, 11 rows

| ID | Item | Assessment |
|---|---|---|
| 2.01 | sum | Used: affine offsets and additive families. |
| 2.02 | difference | Used: quotient defects, congruences and error recurrences. |
| 2.03 | product | Used: multiplier composition and exact monomial identities. |
| 2.04 | quotient | Used: recover only legal integral divisions, not unrestricted field division. |
| 2.05 | remainder | Used: positive-modulus Euclidean representatives; divisor zero is excluded here. |
| 2.06 | integer floor division | Used: distinguish mathematical floor from language-specific signed division. |
| 2.07 | powers | Used: nonnegative exponents in word and resonance identities; negative exponents change domain. |
| 2.08 | root | Specify: positive degree, real/complex domain and a branch; integer existence needs a certificate. |
| 2.09 | logarithm | Used: height budgets only at positive arguments; base positive and different from one. |
| 2.10 | means | Specify: nonzero denominators and real square-root domain; no orbit decrease follows from the name. |
| 2.11 | binomial coefficient | Static: ordinary version has nonnegative indices; signed extensions require a convention. |

## PairProfile 3 — divisibility and gcd/lcm, 10 rows

| ID | Item | Assessment |
|---|---|---|
| 3.01 | divisibility | Used: the actual ring/integer branch guard. |
| 3.02 | common divisors | Used: conductors and shared prime budgets. |
| 3.03 | gcd | Used: exact integrality and accessibility tests. |
| 3.04 | lcm | Used: joint congruence periods and denominator budgets. |
| 3.05 | coprime | Used: invertible affine residue maps and a sufficient independence certificate. |
| 3.06 | pairwise coprime in a set | Specify: a set of moduli is extra data beyond a pair. |
| 3.07 | Bezout coefficients | Used: inverse and congruence recovery; coefficients are not unique. |
| 3.08 | common multiples | Static: multiples of the lcm with a zero convention. |
| 3.09 | divisibility chain | Candidate: can track exact factor budgets; no general raw chain is assumed. |
| 3.10 | aliquot relation | Static: a separate divisor-sum map on positive states. |

## PairProfile 4 — prime-pair relations, 11 rows

| ID | Item | Assessment |
|---|---|---|
| 4.01 | twin primes | Static: joint primality and exact distance two. |
| 4.02 | cousin primes | Static: joint primality and exact distance four. |
| 4.03 | sexy primes | Static: joint primality and exact distance six. |
| 4.04 | consecutive prime gap | Static: primality plus absence of an intervening prime. |
| 4.05 | Sophie Germain pair | Static: joint primality and the specified affine relation. |
| 4.06 | safe prime pair | Static: the reversed Sophie Germain relation. |
| 4.07 | Mersenne pair | Static: the power-minus-one relation does not establish either primality claim. |
| 4.08 | Fermat pair | Static: specify the exponent-index role; primality is separate. |
| 4.09 | emirp pair | Static: fixed-base reversal with unequal values. |
| 4.10 | amicable primes | Specify: if ordinary aliquot amicability is meant, no positive prime pair exists: each prime has aliquot sum one. |
| 4.11 | prime constellations | Specify: a finite offset pattern and joint primality; this is more than a pair unless the pattern has two entries. |

## PairProfile 5 — modular/congruence, 11 rows

| ID | Item | Assessment |
|---|---|---|
| 5.01 | congruence | Used: exact difference divisibility. |
| 5.02 | residues | Used: simultaneous affine-branch data. |
| 5.03 | same residue class | Used: quotient equality; fixed raw division precision is obstructed above. |
| 5.04 | inverse | Used: unit condition before cancellation. |
| 5.05 | order | Used: multiplier order only where it is the correct affine-return invariant. |
| 5.06 | discrete logarithm | Candidate: a relation among units; not an efficient raw-orbit decoder. |
| 5.07 | quadratic characters | Static: specify prime versus composite modulus. |
| 5.08 | primitive root relation | Static: only cyclic unit groups admit generators. |
| 5.09 | CRT compatibility | Used: shared residues must agree modulo the gcd for noncoprime moduli. |
| 5.10 | residue vector | Used: exact product-modulus reconstruction with a decoding range. |
| 5.11 | Legendre/Jacobi symbols | Static: Legendre requires an odd prime; Jacobi one need not imply a square modulo a composite. |

## PairProfile 6 — p-adic tools, 8 rows

| ID | Item | Assessment |
|---|---|---|
| 6.01 | two valuations | Used: retain both exact exponents and infinity cases. |
| 6.02 | p-adic norm of difference | Used: equality to a fixed precision; not an Archimedean distance. |
| 6.03 | p-adic distance | Used: same metric as 6.02, with zero distance only at equality. |
| 6.04 | common p-adic factor | Used: minimum exponent in a gcd, including zero-input conventions. |
| 6.05 | expansion comparison | Used: congruence at an explicit precision; division lowers that precision. |
| 6.06 | unit relation | Used: separate both units, one unit and neither before inverses. |
| 6.07 | square/cube relation | Candidate: require a compatible p-adic witness, not separate finite roots without a transfer. |
| 6.08 | p-adic logarithm ratio | Specify: convergence domain, normalization and a nonzero denominator logarithm. |

## PairProfile 7 — divisor-sum/aliquot, 8 rows

| ID | Item | Assessment |
|---|---|---|
| 7.01 | amicable | Static: both aliquot equations for the same positive pair. |
| 7.02 | sociable | Static: a complete longer cycle, not two local sums. |
| 7.03 | betrothed | Static: both shifted aliquot equations. |
| 7.04 | friendly | Static: equal rational abundancy indices, with positive nonzero denominators. |
| 7.05 | both perfect | Static: two separate static tests; no pair dynamical coupling follows. |
| 7.06 | untouchable relation | Specify: which quantified relation and how global nonexistence is certified. |
| 7.07 | abundance comparison | Static: arithmetic order of divisor-sum defects. |
| 7.08 | practical pair | Static: both positive inputs practical; no raw transport is established. |

## PairProfile 8 — additive number theory, 8 rows

| ID | Item | Assessment |
|---|---|---|
| 8.01 | Goldbach pair | Static: a certificate for one even sum, not the universal Goldbach claim. |
| 8.02 | sum of two squares | Used: exact Gaussian norm form. |
| 8.03 | sum of two cubes | Static: a signed or nonnegative witness must be specified. |
| 8.04 | Waring parts | Specify: the remaining summands, exponent and signs are additional witnesses. |
| 8.05 | taxicab relation | Specify: two distinct unordered power-sum representations of the same value. |
| 8.06 | partition pair | Specify: the common target and positivity of parts. |
| 8.07 | composition pair | Specify: the common target and ordering of parts. |
| 8.08 | additive basis | Specify: a set and coverage range; a pair alone does not define a basis. |

## PairProfile 9 — multiplicative number theory, 8 rows

| ID | Item | Assessment |
|---|---|---|
| 9.01 | product relation | Used: exact affine-word and norm products. |
| 9.02 | common prime factors | Used: support budgets; insufficient to detect power resonance. |
| 9.03 | radicals | Used: support summaries, not exponent-vector independence. |
| 9.04 | multiplicative order | Used: same unit-domain restrictions as 5.05. |
| 9.05 | primitive root | Static: same cyclic-group restriction as 5.08. |
| 9.06 | Dirichlet convolution | Specify: two arithmetic functions, not merely two integer arguments. |
| 9.07 | totient comparison | Static: positive input and exact unit counts; no raw contraction theorem follows. |
| 9.08 | Möbius pair | Static: positive inputs; square factors and support parity determine the values. |

## PairProfile 10 — representation links, 23 rows

| ID | Item | Assessment |
|---|---|---|
| 10.01 | same representation length | Static: base, zero and sign conventions; a coarse height equivalence. |
| 10.02 | same digit sum | Static: loses position and most residue information. |
| 10.03 | same digit product | Static: loses position; zero digits produce many collisions. |
| 10.04 | digit Hamming distance | Specify: equal length or a declared padding rule and sign treatment. |
| 10.05 | edit distance | Static: fixed alphabet and edit costs; not a raw contraction without proof. |
| 10.06 | common prefix/suffix | Candidate: a suffix gives fixed-base precision, with the proved division loss. |
| 10.07 | digit anagrams | Static: equal digit multiset, not equal numerical state. |
| 10.08 | reversal | Static: base and leading-zero convention. |
| 10.09 | concatenation | Static: uses the length of the second string; sign handling must be fixed. |
| 10.10 | palindrome pair | Static: both tests in the same base; no map conjugacy follows. |
| 10.11 | repdigit/repunit | Used: repunit sums give exact cycle constructions; arbitrary repdigits need another bridge. |
| 10.12 | automorphic pair | Static: both width-dependent congruences. |
| 10.13 | Kaprekar pair | Specify: both split conventions; no coupled equation is supplied. |
| 10.14 | happy/sad pair | Static: two outcomes of the different digit-square map. |
| 10.15 | Smith pair | Static: both composite digit/factor identities. |
| 10.16 | Roman relation | Specify: canonical syntax and the proposed relation. |
| 10.17 | Zeckendorf overlap | Static: intersection of nonadjacent Fibonacci supports in a fixed indexing. |
| 10.18 | factoradic relation | Specify: digitwise comparison, rank relation or another exact predicate. |
| 10.19 | continued fraction relation | Specify: integers have one-term canonical expansions; longer expansions are not canonical without rules. |
| 10.20 | Egyptian relation | Specify: choose expansions or quantify common witnesses. |
| 10.21 | Gray distance | Static: fixed code width and metric; raw steps are not Gray-adjacent by definition. |
| 10.22 | two's complement | Used: fixed-width signed overflow checks, not unbounded integer dynamics. |
| 10.23 | IEEE bit relation | Used: precision/rounding negative controls; bit equality need not recover exact integers. |

## PairProfile 11 — bitwise/coding, 11 rows

| ID | Item | Assessment |
|---|---|---|
| 11.01 | AND | Static: require width or an explicit infinite signed-bit convention. |
| 11.02 | OR | Static: same bit-domain convention. |
| 11.03 | XOR | Static: same bit-domain convention; not integer addition. |
| 11.04 | shifts | Used: positive binary division only with exact divisibility and checked exponent; signed rounding differs. |
| 11.05 | popcount difference | Static: width-dependent for negative inputs; not a decreasing raw potential. |
| 11.06 | Hamming distance | Static: XOR popcount in one declared finite-width space. |
| 11.07 | Gray distance | Static: duplicate of 10.21, with the same convention. |
| 11.08 | run-length similarity | Specify: encoding and similarity function; no threshold is canonical. |
| 11.09 | entropy difference | Specify: a probability law or empirical symbol distribution and logarithm base. |
| 11.10 | compression ratio | Specify: codec, input encoding and reference length; not an invariant of the integer alone. |
| 11.11 | checksum/hash | Static: equality under one specified function; collisions do not establish equality of inputs. |

## PairProfile 12 — sequence/figurate, 9 rows

| ID | Item | Assessment |
|---|---|---|
| 12.01 | both triangular | Static: two integral index witnesses. |
| 12.02 | both square | Static: two square witnesses; future raw squareness is not implied. |
| 12.03 | consecutive Fibonacci | Static: one common adjacent-index witness, not unrelated memberships. |
| 12.04 | same figurate type | Specify: the type and admissible index domain. |
| 12.05 | same sequence index | Specify: two sequences/observables; one injective sequence gives equality. |
| 12.06 | sequence ratio | Static: specify indices and exclude a zero denominator. |
| 12.07 | recurrence | Specify: recurrence order, coefficients and enough initial data. |
| 12.08 | linear recurrence pair | Candidate: affine words supply linear formulas, but their branch guards still require separate checking. |
| 12.09 | Lucas/Fibonacci identity | Static: specify the identity, indexing and a joint index witness. |

## PairProfile 13 — algebraic/analytic, 11 rows

| ID | Item | Assessment |
|---|---|---|
| 13.01 | same minimal polynomial | Specify: base field; ordinary rational integers have distinct linear minimal polynomials unless equal. |
| 13.02 | conjugates | Used: quadratic conjugation/norms after moving to a declared number ring; rational integers are fixed. |
| 13.03 | roots of one polynomial | Specify: the polynomial and nontrivial restrictions; any pair is a root pair of some polynomial. |
| 13.04 | same finite field | Used: actual field structures, distinguishing ramified quotient rings that are not fields. |
| 13.05 | matrix representation | Used: exact affine composition and incidence maps with a faithful decoding. |
| 13.06 | determinant | Used: prime-exponent independence and rank certificates; specify the matrix. |
| 13.07 | Taylor coefficients | Specify: one associated function, center and coefficient indices. |
| 13.08 | Fourier coefficients | Candidate: cycle incidence modes require the correct twist and coefficient field; no raw Fourier quotient is assumed. |
| 13.09 | Dirichlet series | Specify: coefficient functions and analytic/formal domain. |
| 13.10 | zeta values | Specify: zeta function, arguments and analytic continuation; no QCD implication is known here. |
| 13.11 | generating function | Candidate: exact affine words give geometric sums; unrestricted orbit generating functions retain the unsolved guards. |

## PairProfile 14 — geometric/combinatorial, 11 rows

| ID | Item | Assessment |
|---|---|---|
| 14.01 | coordinates | Used: a free integral basis gives exact ring-to-coordinate guard recovery. |
| 14.02 | Euclidean distance | Used: complex norm recovery from a positive transverse scale. |
| 14.03 | dot product | Specify: vectors, bilinear form and dimension; two scalars alone give only a product. |
| 14.04 | 3D cross product | Specify: two three-vectors are required, not two scalar integers. |
| 14.05 | slope | Static: denominator nonzero; the vertical case is separate. |
| 14.06 | angle | Specify: vectors, origin/reference axis and zero-vector convention. |
| 14.07 | lattice relation | Used: exact coordinates and adjugate tests; visual proximity is not divisibility. |
| 14.08 | graph edge | Used: a legal raw tick, retaining branch and clock labels. |
| 14.09 | permutation mapping | Used: invertible affine finite maps only with the appropriate unit condition. |
| 14.10 | partition pairing | Specify: partitions of which set/target and the pairing rule. |
| 14.11 | matroid/poset | Specify: ground set, independence/order axioms and a concrete recoverable role. |

## PairProfile 15 — cryptographic, 7 rows

| ID | Item | Assessment |
|---|---|---|
| 15.01 | shared secret | Specify: a group, generator and exponent domain; the integer expression alone is not a secret protocol. |
| 15.02 | Diffie–Hellman | Specify: the same group and transmitted powers; no raw-QCD transport follows. |
| 15.03 | RSA relation | Static: specify modulus/totient and unit exponents; not a Collatz relation. |
| 15.04 | discrete-log pair | Candidate: same unit-group relation as 5.06, with no efficient recovery claim. |
| 15.05 | elliptic-curve pair | Specify: curve, field, points and group law; integers alone are not points. |
| 15.06 | hash collision | Static: equality under one specified hash function; not equality of states or trajectories. |
| 15.07 | pseudorandom states | Specify: generator, state space and law; deterministic QCD iterations are not independent samples. |

## PairProfile 16 — equivalence/order, 12 rows

| ID | Item | Assessment |
|---|---|---|
| 16.01 | equality | Used: exact state equality; duplicate of 1.01. |
| 16.02 | congruence | Used: duplicate of 5.01; raw precision loss remains. |
| 16.03 | same parity | Used: duplicate of 1.05; parity alone is not orbit equivalence. |
| 16.04 | same digit sum | Static: an equivalence once the base is fixed, not a raw congruence. |
| 16.05 | same length | Static: a coarse encoding equivalence, not equal height or trajectory. |
| 16.06 | same valuation | Used: fixed-prime exponent equality, with zero/infinity separately retained. |
| 16.07 | same prime support | Used: support equivalence loses the resonance-detecting exponent ratios. |
| 16.08 | same radical | Used: same support for positive nonzero inputs; duplicate information, not independence. |
| 16.09 | same abundancy | Static: positive nonzero denominators; no QCD equivalence is established. |
| 16.10 | divisibility order | Used: a partial order on positive integers; on signed integers first quotient by units. |
| 16.11 | lexicographic order | Static: encoding-dependent and generally different from numerical order. |
| 16.12 | numeric order | Used: signed integer order, distinct from absolute-value descent. |

## PairProfile 17 — pair parameters, 11 rows

| ID | Item | Assessment |
|---|---|---|
| 17.01 | a, b | Used: the same two states in every jointly asserted relation. |
| 17.02 | base b | Specify: rename B; inherit H03 and prevent symbol collision. |
| 17.03 | modulus m | Used: positive modulus, same one for the compared residues. |
| 17.04 | prime p | Used: one declared prime for both valuations. |
| 17.05 | precision k | Used: one explicit finite precision; higher-to-lower division transfer applies. |
| 17.06 | alphabet D | Specify: same alphabet and decoding convention for both encodings. |
| 17.07 | representation R | Specify: one scheme or a proved conversion between two schemes. |
| 17.08 | sequence S | Specify: one family and jointly compatible index witnesses. |
| 17.09 | number of powers N | Specify: count, exponent and sign domain as in H10. |
| 17.10 | pseudoprime base a_p | Static: fixed base and exact modular test for each input. |
| 17.11 | search limit L | Used: common finite budget; do not upgrade bounded failure to global nonexistence. |

## Dynamical recovery

The general precision theorem is independent of expansion or hitting-time
hypotheses. A global integer classifier would need branch-aware,
clock-aware recovery through arbitrarily many divisions.
Appending static labels does not supply that rule.
The available exact mechanisms retain integer states, legal words, growing
precision or independently proved return budgets. Representation, entropy,
cryptographic and aliquot labels do not by themselves close those budgets.
