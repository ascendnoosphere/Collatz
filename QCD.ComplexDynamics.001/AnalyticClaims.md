<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Analytic extensions and the information they preserve

The raw integer map, its shortcut, a 2-adic coding, and a holomorphic
interpolation are different dynamical systems. The following calculations
identify what each construction retains.

## Entire interpolation and derivative freedom

For the classical shortcut

```math
S(n)=\begin{cases}n/2,&2\mid n,\\(3n+1)/2,&2\nmid n,\end{cases}
```

the entire function

```math
F_0(z)=z+\frac14-\left(\frac z2+\frac14\right)\cos(\pi z)
```

agrees with $`S`$ at every integer. Indeed, substituting
$`\cos(\pi n)=(-1)^n`$ gives the two branches. Its derivative is

```math
F_0'(z)=1-\frac12\cos(\pi z)
+\pi\left(\frac z2+\frac14\right)\sin(\pi z),
```

so $`F_0'(n)=1/2`$ on even integers and $`3/2`$ on odd integers.
This is the classical continuous-extension formula associated with
[Chamberland96], not an interpolation of the raw odd instruction.

Integer-wide agreement does not determine derivatives. Choose distinct
integers $`m_1,\ldots,m_s`$ and any complex numbers $`\delta_1,\ldots,\delta_s`$.
Let $`L_j`$ be their Lagrange basis polynomials and set

```math
P(z)=\sum_{j=1}^s\frac{\delta_j}{\pi(-1)^{m_j}}L_j(z),
\qquad
F(z)=F_0(z)+\sin(\pi z)P(z).
```

At every integer, the added term vanishes. At $`m_j`$, its derivative is
$`\pi(-1)^{m_j}P(m_j)=\delta_j`$. Thus $`F`$ preserves **all** integer
values while changing the chosen derivatives arbitrarily.

For a positive shortcut cycle of length $`L`$ containing $`r`$ odd
instructions, its affine return has slope $`3^r/2^L`$. There must be an odd
instruction: repeated division cannot close at a positive state.
The return offset is positive, so closure gives
$`(1-3^r/2^L)n=B>0`$, proving $`3^r/2^L<1`$.
The cycle multiplier of $`F_0`$ is therefore below one.
Continuity of the derivative of $`F_0^{\circ L}`$ gives a small disk on
which its derivative norm is at most some $`\kappa<1`$; integrating along
a segment gives contraction toward the cycle point.

Derivative freedom can instead make the same integer cycle repelling or
superattracting. Hence even integer-wide agreement does not determine complex
stability. The four finite-node polynomial models in
[ComplexPolynomials.lean](lean/ComplexPolynomials.lean) supply a separate
formal example: the minus-cycle multipliers are $`-5/4`$ and $`0`$.
Their [portraits](README.md#julia-portraits-same-lattice-cycle-different-complex-stability)
illustrate those specified polynomials, not a canonical complex extension.

## Growing seeds and a noninteger profinite limit

Put $`M_N=(N+2)!`$ and $`x_N=2^{M_N}-1`$.
For $`0\le j\le M_N`$, induction gives

```math
S^j(x_N)=3^j2^{M_N-j}-1.
```

For $`j<M_N`$, the state is odd and the shortcut formula proves the
induction step. Thus arbitrarily long odd prefixes are obtained by changing
the seed.

For every fixed odd prime power $`p^k`$, Euler's theorem and eventual
divisibility $`\varphi(p^k)\mid M_N`$ give $`x_N\equiv0\pmod{p^k}`$.
For every fixed $`k`$, one also has $`x_N\equiv-1\pmod{2^k}`$ eventually.
The profinite limit has 2-adic coordinate $`-1`$ and every odd-prime
coordinate zero. It is not a diagonal integer: an integer divisible by
all powers of one odd prime must be zero, whose 2-adic coordinate is not
$`-1`$.

The factorial must be in the **exponent**. The different sequence
$`2(N+2)!-1`$ tends to $`-1`$ at the odd places too.
Neither sequence supplies a divergent trajectory of one fixed positive seed.

## Parity coding: a homeomorphism, not invertible dynamics

For odd $`c`$, the shortcut $`S_c`$ extends to $`\mathbb Z_2`$ with inverse
branches

```math
f_0(z)=2z,\qquad f_1(z)=\frac{2z-c}{3}.
```

Their images are the disjoint even and odd cylinders. Each scales 2-adic
distance by $`1/2`$. A finite word of length $`h`$ consequently determines
one ball modulo $`2^h`$. Nested compatible balls determine one 2-adic
point by completeness. Conversely, every point has its unique parity word.

If two words first differ at index $`h`$, their residual points lie in
opposite parity cylinders, at distance one; the common inverse prefix scales
that distance to $`2^{-h}`$. The coding is therefore an isometry for the
usual symbolic ultrametric and conjugates $`S_c`$ to the one-sided shift.

The coding is a homeomorphism. The shift and the shortcut are two-to-one,
not homeomorphisms of the state space: both $`0`$ and $`-c/3`$ map to zero.
A conjugacy does not turn a noninvertible dynamical map into an invertible one.

## Reciprocal compactifications

For $`A\subseteq\mathbb Z_{>0}`$, put
$`K_A=\{0\}\cup\{1/a:a\in A\}`$.
Its only possible accumulation point is zero, so it is compact and countable.

Suppose $`\#(A\cap[1,X])\le CX^\beta`$ for $`X\ge1`$ and $`\beta\ge0`$.
Cover the points with $`a\le X`$ individually and cover the remaining
points by intervals in $`[0,1/X]`$. The number of length-$`\varepsilon`$
intervals needed is at most

```math
N_\varepsilon(K_A)\le CX^\beta+1+\frac1{\varepsilon X}.
```

Choosing $`X=\varepsilon^{-1/(1+\beta)}`$ gives upper box dimension at most
$`\beta/(1+\beta)`$. Its Hausdorff dimension is zero: for any positive
$`s,\delta`$, enumerate its points and give the $`j`$th point an interval
whose $`s`$th power of diameter is below $`\delta 2^{-j}`$.

This countable real compactification is not the uncountable symbolic space,
its 2-adic image, or a polynomial Julia set. Moving between these objects
requires an explicit map and estimates for the property being transferred.

## Sources and formal scope

[Chamberland96] Marc Chamberland, *A Continuous Extension of the 3x+1
Problem to the Real Line*, *Dynamics of Continuous, Discrete and Impulsive
Systems* 2 (1996), 495–509.
[Author-hosted paper](https://chamberland.math.grinnell.edu/papers/3x_1996.pdf).

Related formulations appear in the independent local manuscript
`/home/dell/collatz/FINALEE.MD`, sections 14.1, 14.16 and 14.38.
The calculations above are written proofs. The linked Lean module proves
the finite polynomial identities, derivatives and exterior growth; it does
not formalize every general analytic or 2-adic statement on this page.
