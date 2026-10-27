<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Classical positive-capture proof obligations

Historical inventory: 85 maintained pages, comprising 83 `QCD.*` pages,
`Foundations.Main.StartHere`, and `Library.SourceCatalogue.001`. The original
inventory was read-only; subsequent additions are noted below. Target: `T(n)=n/2` for even `n`, `(3n+1)/2` for odd `n`; prove `forall n>0 exists s, T^s(n)=1`.
Labels: **[a]** parameter mismatch, cannot apply to `(3,1,2)`; **[b]** density/measure/statistics/finite census only; **[c]** produces a smaller parent; **[d]** classifies/excludes cycles. Clocks: **raw** one division-first instruction; **SC** one shortcut tick; **ret** one first-division return; **word** one binary/exponent letter; **2-adic** Haar time.

## 1. Inventory

| # | Page | Mechanism | Exact class | Strongest proved conclusion | Clock | Explicit non-claim |
|---:|---|---|---|---|---|---|
| 1 | Foundations.Main.StartHere | Legal-word algebra; affine `(P,Q,B)` composition; conductor; marked-graph capture transport | Signed `q,c,d`, `abs(d)>=2`; arbitrary words | Successful word equals first `k` raw branches; closure forces `(Q-P)n=B`; same-time and accumulated-time capture transfer | raw | Closure equation does not imply intermediate guards; rational fixed point is not legality |
| 2 | Library.SourceCatalogue.001 | Source-finding inventory; no theorem | Corpus metadata | Locates and checks source records; separates catalogue from proof | n/a | Catalogue is not a theorem database; no mathematical claim |
| 3 | QCD.SwarmAttack.001 | Audit charter and status index | Twenty workstreams | Records target, labels, and the `R_E` residual | n/a | No proof; residual explicitly open |
| 4 | QCD.ClassicalCoalescence.001 | Shortcut smaller-parent joins; explicit legal words; subtract disjoint cylinders | Positive `n`, shortcut `T` | Every `n>1` outside `R_E` has parent `p<n`, `123p<=118n`; depth `<=ceil(log n/log(123/118))`; `d(R_E)=6689147268412473047/315179916321896792064=0.021223` | SC; raw clocks tabulated per cylinder | Capture or parent existence on `R_E` not proved; the two specified bounded-word certificate types cannot finitely cover the 27-cell; not a divergent orbit |
| 5 | QCD.ClassicalRecovery.001 | Embed `(3,1,2)` in `(3*2^a, 2^a*3^b, 2)`; absorb into `3^b Z` | `a,b>=0`, positive seeds | Positive capture for `F_{a,b}` iff classical positive capture; tail into `3^b Z` after `<=b` affine events; target cycle primitive period `a+3` | raw, variable compression | Equivalence is not proof; not pointwise; `(3u,u,2)`, `u!=1`, is not identified |
| 6 | QCD.TimeCompression.001 | Remove common power `d^a` | `q=d^a Q`, `c=d^a C`, signed | `G^k(n)=F^{k+aR(k,n)}(n)`; forward capture; height strictly drops if `a>0` | compressed and raw | `a=0` for `(3,1,2)`; no capture conclusion |
| 7 | QCD.TimeCompression.002 | Full block recovery; primitive periods | Signed, `abs(d)>=2`, any `a` | Boundedness, full escape, periodicity equivalent; target capture bijective if target is division-closed (`1` qualifies); primitive raw period `h+aR` | raw | Not one-step conjugacy; no convergence |
| 8 | QCD.Scaling.001 | Coprime scaling; offset entry | `gcd(h,d)=1`; `gcd(c,d)=1`, `c` divides `q^k` | `F_{q,hc,d}^s(hn)=hF_{q,c,d}^s(n)`; entry into `cZ` after `<=k` affine events; all-target capture equivalence | raw | `c=1` makes classical case vacuous; core capture not solved |
| 9 | QCD.Scaling.002 | Supported offset `S` divides `C` | `S` divides `C`, `gcd(S,D)=1`, `S` divides `Q^k` | Common entry `S m` and exact scaled tail after `<=k` affine events; capture and cycle recovery at same raw period; maximal supported factor extracted | raw | Not pointwise; `S=1` trivial for `(3,1,2)` |
| 10 | QCD.LocalJoin.001 | One exact raw cylinder, two prefixes | `(3,1,2)`, `n=11003+2^20 t` | `C^32(n)=C^6(9915+944784t)=33466+3188646t`; `p=9915+944784t`, `100p<=91n`; first meeting | raw 32 and 6 | One cylinder; no exhaustive cover |
| 11 | QCD.CaptureChain.001 | Well-founded chain of legal joins | Any raw map, `abs(d)>=2` | A chain `m_0>...>m_t=1` of legal joins forces capture of `m_0` in at most `abs(m_0)` states | raw | Existence of the chain is not proved |
| 12 | QCD.RecursiveClose.001 | Certified capture time from a join | Shortcut `T` on naturals | `T^a(n)=T^b(p)` and `T^t(p)=1` imply `T^{tau(a,b,t)}(n)=1` | SC | `tau` is not least; does not generate parents |
| 13 | QCD.ThreeAffineClosure.001 | Eliminate three odd-return equations; product window | Positive odd, 3 edges; `q=3`, `r<=5` | 3-edge closure iff `q` odd, `Delta=2^K-q^3>0`, `Delta` divides `B`; classical `r<=5` forces all states `1` and all exponents `2` | 3 odd-return ticks; `K` SC; `K+3` raw | Arbitrary `r` not classified; no uniform `K` bound |
| 14 | QCD.TwoAffineEven.001 | Two-return elimination at even total length | Positive `q,n,y`, `a+b=2t` | `a=b=t`, `q=2^t-1`, `n=y=1` | division counts | Unit solution repeats one odd block; not primitive two-state cycle |
| 15 | QCD.TwoAffineCongruence.001 | Modular partner divisibility | `Delta=2^K-q^2` odd | Divisibility transfers between `a` and `K-a`; equal quotients force `K=2a`, `q=2^a-1`, `n=y=1` | `K` divisions | Even `K` with quotient `>=3` not excluded; no Nagell/Beukers |
| 16 | QCD.TwoAffineWindow.001 | Clear denominator positivity test | Odd `K>=3`, odd `q` | `2^K<=(q+1/3)^2` iff `9*2^K<=(3q+1)^2`; unique odd bracket | n/a | No cycle is asserted |
| 17 | QCD.ReverseBound.001 | Product bound on two-return cycle | `q` odd, `x,y` positive odd | Even `K=a+b` with `x,y>=2` impossible; sharp at `x=y=1`, `q=3`, `a=b=2` | division counts | Odd `K` and `>=3` odd states not covered |
| 18 | QCD.Relations.Cycles.001 | Four raw parameter slices | `d>=2`; `d=2,q=2c+1`; geometric; full-access; `q=d+1,c=d-1` | At `d=k=2` the full-access slice is `(3,1,2)` and the unit cycle `1->4->2->1` is primitive; `c=1` odd-stratum invariant is trivial; other slices avoid `1` or reach only powers | raw | Per-slice only; no uniform theorem |
| 19 | QCD.Relations.Core.001 | Multiplier `d-1` return map | `q=d-1`, `d>=2`, `c>=1`, positive | Return core `{1,...,c}`; every orbit is trap or eventually periodic; corner `c=d+1` cycle `d+1->d(d+1)`, zeta `1/(1-z^2)` | return, 1-2 raw | At `d=2`, `q=1`, not classical; no divergence density |
| 20 | QCD.Repunit.001 | Divisor `S_k(q)`, offset one | `q>=2`, `D=S_k(q)` | `ord_{S_k}(q)=k`; seed `1` cycles length `k` through `S_2,...,S_k`; residue walk has `k` distinct values | raw | `q=3,k=2` is `(3,1,4)`, not `(3,1,2)`; orbit classification open |
| 21 | QCD.RepunitDivisor.001 | Repunit identity | `q>=1`, `k>=0` | `q^k=1+(q-1)G_k(q)`; `G_k` divides `q^k-1`; `gcd(q,G_k)=1`; affine return mod `G_k` | affine steps | No dynamics or classification |
| 22 | QCD.DyadicDynamics.001 | `q+c` odd dichotomy; 2-adic golden mean; statistics | `q+c` odd, `abs(q)>=2` (integer); odd `q,c` (2-adic) | Fixed anchor or full escape; `q=2^k-1,c=1` primitive unit cycle length `k+1` (`k=2` is classical); odd `q,c` gives golden-shift conjugacy, entropy `log phi`, zeta `1/(1-z-z^2)`, mean `h/3` | raw; 2-adic | Integer capture not classified; `q+c` even excludes `(3,1,2)` from dichotomy; 2-adic results are not integer results |
| 23 | QCD.ComplexCohomology.001 | Graph and twisted cycle cochains; holonomy | Finite cycles, any coefficient field | `H^1` dimension is component count; twisted cochain recovers `(P,B)`; minus cycle at `17` has period `18`, defect `139`, quotient dimension one over `F_139` | cycle length | No Galois/etale theory; cohomology forgets guards and length |
| 24 | QCD.EqualHalves.001 | Split a cycle word into equal halves | Odd `q`; `U,V` length `h`, `r` ones, `Q=2^h-q^r>0` | Concatenation closes iff `M=2^h+q^r` divides `A(U)-A(V)` and `Q` divides `A(U)+A(V)`; factors can separate | word | No cycle realization is assumed |
| 25 | QCD.OneBit.001 | Adjacent swap `p01s` versus `p10s` | Classical SC, arbitrary `p,s` | No closed word whose consecutive halves differ by swapping an adjacent `0/1`; `M` cannot divide `mu` | SC | Specified word family only; the ordinary word `10` is outside it |
| 26 | QCD.NoCrossing.001 | Move two indices with no support between | Binary words, equal halves | `M=2^h+3^r` never divides the difference; three-crossing extension; four or more crossings open | word | Difference condition is not sufficient for closure |
| 27 | QCD.HammingGap.001 | Antipodal Hamming distance | Binary words of length `2h` | `H=0` iff doubled, `H=2` iff a transport exists, otherwise `H>=4`; witness within first `h` rotations | word | Needs a separate transport exclusion to apply to cycles |
| 28 | QCD.CyclicGap.001 | Two-run cyclic words | Exponents `{1,2}`, word `1^p2^q` | Positive closure impossible when the second block has length `<=2` (with `p=1,q=2` failing `5` divides `1`) | exponent sum | Second block `>=3` and four-block words open |
| 29 | QCD.CarryGap.001 | Nearest-integer carry energy | Odd `q,c`; word `w` | `E(w)=0` or `E(w)>1/2`; for `q=3`, word `10` has energy zero | word | Zero energy is not excluded; no capture |
| 30 | QCD.SharpEnergy.001 | Energy of one block word | `b,r>=1`, word `0^b1^r0^{b-1}101^{r-1}` | `E=2^h/(2^h+3^r)`; `E>1/2` iff `3^r<2^h`; for fixed `b`, `E->0` | word | No integer reconstruction |
| 31 | QCD.PhaseRigid.001 | Rational phase defect | Odd `q,c`; cyclic word | Maximum defect is `0` or at least `2/(q+2)`; for `q=3` the threshold is `2/5` | word | Individual defects may be smaller; no smooth extension |
| 32 | QCD.LogGap.001 | Product of eight positive factors | Real `r_i` | Deficit at least `log(256/243)` forces product `<=243/256`; constant is optimal | block of 8 | Not proved for Collatz branches |
| 33 | QCD.Braid.001 | Braid modulo `D^2`, `q=D+1` | `abs(D)>=2`, `D` not divide `c`, congruence | Source/parent word relation; at `q=3,D=2,c=1,a=1` coefficient is zero and no pair exists | two-step | Divisibility does not produce a pair; positivity not claimed |
| 34 | QCD.ThreeStuck.001 | Inverse odd step valuation | `z` natural, `I(z)=(2z-1)/3` | `v_3(I^k(z)+1)=b-k`; exactly `b` integral inverse steps | inverse odd | No forward capture |
| 35 | QCD.OddRoot.001 | Inverse odd root | `z!=-1` | `R=2^b m-1`; exactly `b` steps integral; `0<=z` implies `0<=R<=z` | inverse odd | `R` may be divisible by `3`; no capture |
| 36 | QCD.AncestralJoin.001 | Inverse odd then shifted halving | `z=2^a3^b u-1`, congruence | `I^b(z)=2^{a+b}u-1`; `H(I^b(z))=2^{a+b-1}u-1`; `u=(-1)^b mod 4` | `b` steps | Not raw division; no classical conclusion |
| 37 | QCD.BurstGrowth.001 | String of ones | Shortcut, `n=2^a-1` | `T^k(2^a-1)=3^k2^{a-k}-1`; `a` odd steps reach `3^a-1` | SC | No capture |
| 38 | QCD.ParentRise.001 | Explicit orbit of `27`; parent above seed | Shortcut | `T^23(27)=445`, `T^26(27)=167=T^3(445)=T^2(222)`, and `222>27` | SC | Parent above seed; no capture |
| 39 | QCD.OneExcursion.001 | One odd run then exit; coefficient signs | `n=2^a u-1`, `a>=2`, `u` odd | Exit `y=(3^a u-1)/2`; quarter/half parents below `n` only for `a<=2/3`; six-step exit is at least `2n+1` | SC | Finiteness of residual excursions not proved; five-step cutoff not uniform |
| 40 | QCD.FamilySplit.001 | Even row | Shortcut, `n` even | `T(n)=n/2` and `p=n/2<n` | SC | Not a cover of the integers |
| 41 | QCD.MirrorSign.001 | Mirror quotient `(3n-1)/2^v` | Positive or negative `n` | Sign preserved on integral schedules; `1` fixed; `5<->7` | `v` | Not `3n+1`; no cycle classification |
| 42 | QCD.InverseBudget.001 | Denominator budget for ascending words | `q,c,D` positive | Legal `p<m` forces `D^e<(q+c)^s`; fixed affine depth gives finite exhaustive search | word counts | Growing affine depth is a different problem |
| 43 | QCD.BeukersList.001 | Squares in dyadic equations | `D=7,23` | Even exponents classified; all `n<=32`; every Mersenne `D=2^k-1` has two representations | n/a | Odd `n>32` open; no affine cycle |
| 44 | QCD.NagellList.001 | Five explicit dyadic square solutions | Fixed pairs | `(1,3),(3,4),(5,5),(11,7),(181,15)` | n/a | Not exhaustive |
| 45 | QCD.ResidueLeakage.001 | Residue cylinders; drift; prime-square nonunit family | `q>=2,c>=1,D>=2,gcd(q,D)=1`; `m<D` versus `m=D` | `m<D`: exactly `m^h` classes mod `D^h` with `h` divisions, infinitely-dividing density zero, complement density one; `m=D`: exact product law and negative drift exactly for `q=3,D=2`, odd `c`; classical `E(X)<=(22+2/beta)X^{1-alpha}` and fixed-fraction descent in `O(log n)` | raw | Density and stopping time only; classical has `m=D`, so density-one escape is inapplicable; not universal capture |
| 46 | QCD.ResidueAccess.001 | Zero orbit of the affine residue map | `q>=2,c>=1,D>=2` | Return iff `M(q,c,D)` divides `q^j-1`; period `m<=D`; prime full access iff `q=1 mod p`; classical `M=4`, `m=2=D` | affine residue | Not same-clock raw; no capture |
| 47 | QCD.Discriminator.001 | Neutral translation `D=q^k`, `c=tD` | `q>=2`, `k,t>=1`, `q` not divide `n` | If `gcd(q,t)` not divide `n`, escape; otherwise least delay gives return `J` with `qJ<=n+A`, descent above `N_0` | block `k+1` | Return below floor may change class; classical is not in the family |
| 48 | QCD.OffsetObstruction.001 | Gcd strata at `D=2,q=3` | `c>=0` positive | If `m` divides `c` and `gcd(m,6)=1`, the gcd stratum is invariant; `c,4c,2c` cycle for odd `c`; even `c` makes every positive orbit unbounded; basin density `<=1/m` | raw | `c=3^a` has only trivial `m`; no capture |
| 49 | QCD.OddBurst.001 | Source-weighted initial odd run | Classical SC, odd `n>=3` | Occupation `<= (2560/27)(7/16)^A`; total `<=1120/27` | initial SC run | Initial run only; no individual capture |
| 50 | QCD.RhoComparison.001 | Telescoping weights | `rho=1/(n(n+1))`, `mu=2/(n(n-1))` | `2rho<=mu<=4rho` for `n>=3`; convergent masses; quotient bounds | n/a | No orbit conclusion |
| 51 | QCD.AffineEscape.001 | Gcd division barrier | `q>=2,c>=1,D>=2`, `gcd(q,D)` does not divide `c` | No affine image is divisible; exact tail `q^j x+cG_j`; every positive seed escapes | raw | Classical gcd `1` divides `c=1`, so inapplicable |
| 52 | QCD.Additive.001 | Unique access and finite core | `q=1,c>=1,D>=2` | Unique `l<L`; endpoint `(n+lc)/D`; core `N<=c`; entry `hL` | raw | `q=1` only |
| 53 | QCD.Additive.002 | Inverse-multiplication cycle classification | `q=1,c>=1,D>=2` | Primitive cycles are full inverse-multiplication orbits mod `t` in window `M`; period `h+(D-1)/t sum m_i` | raw grouped | `q=1` only |
| 54 | QCD.Additive.003 | All-seed additive outcome | `q=1,c>=1,D>=2` | Periodic or exact escaping affine tail; periodic iff `gcd(c,D)=1`; outcome budget `u<=(h+N)L` | raw | No `q!=1` |
| 55 | QCD.Homogeneous.001 | Independent homogeneous escape | `c=0,q,D>=2`, independent | Injective orbit and full escape | raw | `c=0` only |
| 56 | QCD.Homogeneous.002 | Dependent homogeneous periodicity | `q^a=D^b`, `q=t^u,D=t^v` | Primitive period `u+v`; height `<=qDn` | raw | `c=0` only |
| 57 | QCD.Homogeneous.003 | Unit multiplier | `q=1,c=0,D>=2` | `n=rD^k`, orbit `rD^{max(k-j,0)}`; fixed points are exactly the `D`-free integers | raw | `q>=2` not covered |
| 58 | QCD.CommonBase.001 | Super-offset common base | `Q=t^u,D=t^v,C=t^a s`, `0<u<v`, `gcd(u,v)=1`, `a>=u+v` | Every nonzero signed seed escapes and eventually has the offset sign; zero is the only periodic point; exact sweep ray | raw, sweep `u+v` | No classical `(3,2)`; no negative divisor |
| 59 | QCD.CommonBase.002 | Gcd rebasing | As above, `g=gcd(u,v)` | Same conclusions with `T=t^g`, sweep `(u+v)/g` | raw | Positive divisor, `0<u<v` |
| 60 | QCD.CommonBase.003 | Arbitrary exponent order | `u,v>0`, `a>=u+v` | Every nonzero signed seed escapes; compression; event clock `1+floor((k+u)/v)` | raw | Negative divisors and other regimes separate |
| 61 | QCD.ProfileDrop.001 | Division-free escape versus zero-avoiding residue cycle | `abs(q)>=2`, `abs(d)>=2` | Division-free escaping seed exists iff `f(r)=qr+c mod abs(d)` has a zero-avoiding cycle; otherwise every seed is divisible by time `<abs(d)`; classical mod 2 has `1->0`, so every seed divides within two ticks | raw | No post-division capture; `p=2` zero-access needs `4` divides `q-1`, false for `q=3` |
| 62 | QCD.SignedTraps.001 | Trapped-orbit itinerary | Signed `q,c,d` | `q^j n+cT_j`; multiplier classification; trapped iff the residue walk avoids zero | raw | Only trapped orbits |
| 63 | QCD.SignedCore.001 | Linear core lemma | `A<m`, `m abs(H(n))<=A abs(n)+B` | Entry into radius `N=floor(B/(m-A))`; eventual periodicity | arbitrary | `H` is not identified with a return |
| 64 | QCD.UniformContraction.001 | Half-contraction entry | `2 abs(T(n))<=abs(n)` outside `R` | Entry `k<=abs(n)`; affine majorant fixed point | arbitrary | Contraction is a hypothesis, not a theorem |
| 65 | QCD.SignedReturn.001 | Affine prefix; first hit; one quotient | Signed, `abs(d)>=2` | `T^j(n)=A_j` on a division-free prefix; first-hit quotient; magnitude bound | raw | One division only |
| 66 | QCD.SignedReturn.002 | Raw and affine guard equivalence | Same | Earlier affine hit iff earlier raw hit; one division | raw | Quotient may still be divisible |
| 67 | QCD.SignedReturn.003 | Exact product of a signed division | `d` divides `a` | `d*(a/d)=a` and `abs(d)*abs(a/d)=abs(a)` | n/a | No remainder |
| 68 | QCD.SignedReturn.004 | Triangle bound on a return | Same | `abs(A_j)<=abs(q)^j abs(n)+abs(c) abs(U_j)`; denominator times return bounded | raw | No contraction |
| 69 | QCD.SignedReturn.005 | Residue criterion | Same | First hit iff the residue walk first hits zero; congruent seeds have the same hit | raw | No existence |
| 70 | QCD.SignedReturn.006 | First-hit clock | Same | First hit `j<abs(d)`; pre-hit residues distinct | raw | Hits may never occur |
| 71 | QCD.SignedReturn.007 | Congruence transport | Same | `A_j(n+td)=A_j(n)+q^j td`; first hit depends only on `n mod d` | raw | No magnitude control |
| 72 | QCD.SignedReturn.008 | No uniform affine bound on one class | Same | If `abs(q)^j>=abs(d)` at a hit, no `A<abs(d)` bounds the return on that class | raw | Negative result only |
| 73 | QCD.SignedReturn.009 | Immediate return at exponent zero | `q,c,d` | `j=0` is a hit iff `d` divides `n`; return `n/d` | raw | Only immediate return |
| 74 | QCD.SignedReturn.010 | Zero multiplier | `q=0` | Trapped orbit reaches `c`; `c` is fixed | raw | `c` is not necessarily `1` |
| 75 | QCD.SignedReturn.011 | Unit multiplier | `q=1` | Trapped orbit translates `n+jc`; escapes if `c!=0` | raw | Only trapped orbits |
| 76 | QCD.SignedReturn.012 | Negative unit multiplier | `q=-1` | Even times fix, odd times send `n` to `c-n`; two-cycle | raw | Reflection only |
| 77 | QCD.SignedReturn.013 | Hit-or-trap dichotomy | Signed | Every orbit has a first hit or is trapped; exhaustive | raw | No classification of hit times |
| 78 | QCD.SignedReturn.014 | Closed offset sum | `q>=2` | `(q-1)U_j=q^j-1`; `U_j=(q^j-1)/(q-1)>=0` | n/a | Arithmetic only |
| 79 | QCD.SignedReturn.015 | Uniform hit bound implies core | Every seed hits; `A<abs(d)`, `abs(q)^{j(n)}<=A`, `abs(c)U<=B` | `abs(d) abs(H(n))<=A abs(n)+B`; core entry and periodicity of the return map | return | Every-seed hypothesis not proved; classical slope `3>=2` fails |
| 80 | QCD.SignedReturn.016 | First hits for `q=2,c=1,d=3` | Specific record | Seed `1` hits at `1` and returns `1`; seed `4` hits at `1` and returns `3`; seed `2` never hits | raw | Example only |
| 81 | QCD.LatticeEntry.001 | Entry into `cZ` before division | `D` not divide `c`, `gcd(c,D)=1`, `c` divides `q^k` | `A^k(n)` is divisible by `c` for every integer `n` | `k` affine | Classical `c=1` is vacuous; not capture |
| 82 | QCD.ComplexLattice.001 | Imaginary quadratic lattice; independent/dependent magnitudes | `c=0`, `abs(q),abs(d)>=2`; arbitrary integer `c` | Independent gives full norm escape; dependent gives eventual periodicity with coordinate bounds; every nonreal seed escapes for any `c`; odd `c` in `(3,c,2)` has a division-free tail | raw | Integer axis retains the signed integer problem; no positive integer capture |
| 83 | QCD.ComplexDynamics.001 | Survey of lattice, residue-wise, and polynomial conventions | Separate state spaces | Exact census; 9,312 proved off-axis escapes per scalar family; 45 quotient cycles reached | ticks | Lattice textures are not Julia sets; quotient cycles are not raw cycles |
| 84 | QCD.GaussianDynamics.001 | Exact Gaussian division; Bezout escape | `Z[i]`, `c=0`, `N(q),N(d)>=2`, `aq+bd=1` | Division prefix `2^r<=N(z)`; full norm escape | raw | No offsets; no integer capture |
| 85 | QCD.QuadraticArithmetic.001 | Quadratic-order division; dyadic criticality | `Z[w]`, `w^2-tau w+nu=0` | Exact division criterion; `q=2,c=0,d=1+sqrt(-D)` has period `12` for `D=1,3` and escape otherwise; dyadic instruction period `e` and growth | raw | Not classical |

## 2. Composition toward `(3,1,2)` and the break

```
Foundations: legal-word algebra, conductor
  |-- Scaling.001/002, TimeCompression.001/002 — normalization; classical c=1, a=0, no strict reduction
  |-- ClassicalRecovery — (3,1,2) is the a=b=0 base; positive-capture equivalence only, no descent
  |-- ResidueAccess -> ResidueLeakage — boundary m=2=D; density-one strict descent unavailable, negative drift survives
  |-- ProfileDrop/SignedTraps/SignedReturn.001-016/SignedCore/UniformContraction — conditional core
  |        `-- requires first-hit slope abs(q)^{j(n)}<abs(d); classical 3^1=3>=2  [BREAK]
  `-- ClassicalCoalescence — parent cover: n>1 outside R_E has p<n, 123p<=118n, depth O(log n)
           `-- R_E, density 0.021223 — least counterexample must lie here
                  |-- 27-cell E_L: L odd increases after tick ten; restricted finite covers fail
                  `-- [OPEN] legal join to a smaller parent, or capture, on R_E

Cycle branch (independent): EqualHalves/OneBit/NoCrossing/CyclicGap/HammingGap/PhaseRigid
  |-- TwoAffineEven + TwoAffineCongruence + ReverseBound — at most two odd states
  `-- ThreeAffineClosure — at most five odd states, only the unit cycle
         |-- SwarmChecks: exhaustive product-window exclusion at ranks six through nine
         `-- [OPEN] ten or more odd states and universal exclusion of divergence
```

Status: **CANDIDATE REDUCTION**. Recovery is proved and the parent label decreases, so a least counterexample lies in `R_E`; but the residual keeps an all-seed statement of the same logical strength, so the cover is a certified localization, not a certified decrease of proof difficulty. The cycle branch excludes cycles only; the parent branch says nothing about cycles.

## 3. Which results actually reach `(3,1,2)`

**(a) Parameter mismatch; cannot apply.** `Additive.001-003` (`q=1`); `Homogeneous.001-003` (`c=0`); `AffineEscape` (`gcd(3,2)=1` divides `c=1`); `CommonBase.001-003` (`3`, `2` multiplicatively independent); `Discriminator` (`2!=3^k`); `Relations.Core` (`q=d-1=1` at `d=2`); `Repunit.001` (divisor `S_k(3)=4,13,...`, not `2`); `Scaling.001/002` (`c=1`, `S=1`); `TimeCompression` (`a=0`); `LatticeEntry` (`c=1` vacuous); `ComplexLattice`, `ComplexDynamics`, `GaussianDynamics`, `QuadraticArithmetic` (nonreal states or `c=0`); `ComplexCohomology` (different state space); `BeukersList`, `NagellList` (arithmetic only); `MirrorSign` (`3n-1`); `OffsetObstruction` (only the trivial stratum at `c=1`); `Braid` (no classical solution pair).
Near miss: `DyadicDynamics` gives a complete integer dichotomy only for `q+c` odd; `(3,1,2)` has `q+c=4`, so the dichotomy excludes the classical cell. Its 2-adic golden-mean theorem applies (odd `q,c`) but yields only Haar/2-adic statements.

**(b) Applies, but only density, measure, statistics, or finite census.** `ResidueLeakage` is strongest: at `m=D=2` the density-one escape theorem fails, but negative drift gives a power-saving stopping time — all but `O(X^{1-alpha})` seeds `<=X` fall below their initial value in `O(log n)` raw ticks, `beta=65536/84375`, `alpha=log(1/beta)/log(256/beta)>0`. This is not capture. Also `OddBurst` (initial-run occupation), `RhoComparison` (weight comparison, no orbit), `DyadicDynamics` (2-adic statistics/entropy), `ComplexDynamics` (finite census), `OffsetObstruction` (`1/m` basin density, vacuous at `c=1`).

**(c) Produce a smaller parent.** `ClassicalCoalescence` covers every positive seed outside its stated residual (`R_E` residual, density `0.021223`, `123p<=118n`, logarithmic depth). `LocalJoin` gives one exact raw cylinder (`100p<=91n`). `CaptureChain` and `RecursiveClose` turn a join into a capture time. `OneExcursion` covers only `a<=3`; `FamilySplit` only the even row; `Scaling`/`TimeCompression` reduce coefficient height, not the seed. `ClassicalRecovery` enters `3^b Z` but its base case is the target.

**(d) Classify or exclude cycles.** `ThreeAffineClosure` is strongest: every positive classical closure with at most five odd states is the unit cycle (all states `1`, all division exponents `2`). `TwoAffineEven`, `TwoAffineCongruence`, `ReverseBound` settle two odd states (even total division length impossible above `1`). `Relations.Cycles` proves `1->4->2->1` primitive of raw length `3`; `Relations.Core`, `Repunit.001`, `DyadicDynamics`, `ClassicalRecovery` give other exact families. `EqualHalves`, `OneBit`, `NoCrossing`, `CyclicGap`, `HammingGap`, `PhaseRigid`, `CarryGap`, `SharpEnergy`, `LogGap` are word-level fragments, not a classification. The added [rank-six-through-nine check](Agent11.md) extends the finite exclusion.
No page excludes all non-unit cycles or all positive divergent orbits.

## 4. Earliest open step

The parent argument needs three statements:

1. Every $`n>1`$ outside $`\mathcal R_{\mathrm E}`$ has a legal join to
   a parent $`0<p<n`$ with $`123p\le118n`$. The ClassicalCoalescence
   article proves this.
2. If every residual seed also has a positive smaller parent, strong
   induction gives universal capture. A meeting point may exceed $`n`$;
   only the parent label must decrease. If a captured parent hits one before
   the meeting time, its later trajectory is still on $`1\leftrightarrow2`$,
   so the source still reaches one after joining it.
3. For every $`n\in\mathcal R_{\mathrm E}`$, find such a parent.
   This is the open statement.

Conversely, capture of a residual $`n>1`$ gives the parent one by taking
its hitting-time join. Thus the missing parent statement is not certified
as an easier theorem merely by writing it as a join. The proved cover
localizes a least counterexample and bounds parent-chain depth outside the
residual. It does not supply the missing residual parents.

The 27-cell obstruction has a narrower conclusion than "no fixed-depth
parent rule." Its first ten ticks are the displayed prefix, followed by
$`L`$ odd increases. The TeX theorem excludes finite dyadic covers using
fixed source/parent words or the five specified shortenings. It does not
exclude all smaller-parent joins. [Report 07](Agent07.md) separately rules
out fixed-precision uniform direct descents, and [Report 10](Agent10.md)
allows arbitrary odd modulus factors in that direct-descent obstruction.

## 5. A proposed extension that fails immediately

The earlier next test treated the second burst length $`b`$ on
$`n(t)=27+1024t`$ as a free parameter. It is not. The exact identities are

```math
n(t)=2^2(7+256t)-1,\qquad
3^2(7+256t)+1=2^6(1+36t).
```

Since $`1+36t`$ is odd, the inherited parameters are $`a=2`$, $`b=5`$,
and $`v=1+36t`$. For $`t\equiv41\pmod{64}`$,

```math
3^bv=243(1+36t)\equiv255\pmod{256}.
```

It can satisfy neither the proposed residue 129 nor the applicable paired-tail
residue 43 modulo 256. This refutes that particular extension on the whole
$`\mathcal E_6`$ family; increasing a search bound on $`b`$ would not help.
Any later-prefix construction must derive new parameters from the actual
later state rather than vary these fixed initial valuations.

The original report also mentioned temporary finite first-descent diagnostics
for $`6\le L\le30`$. Their program is not retained. They do not establish
a uniform depth bound and are not used in the obstruction proofs.

## 6. Remaining obligation

For every $`n\in\mathcal R_{\mathrm E}`$, prove that there are
$`p,a,b\in\mathbb N`$ with $`0<p<n`$ and $`T^a(n)=T^b(p)`$, or prove
capture of that residual directly. A uniform parent contraction factor would
also bound chain length, but no such residual factor is proved here.
Cycle exclusion at ranks six through nine closes only a finite cycle
subproblem; it leaves both longer cycles and divergence outside its scope.
