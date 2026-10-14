<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Integral cycle arithmetic and marked obstructions

Ordered affine equations carry more information than an unmarked graph.
This page proves the cyclic integer quotient, reconstructs all integral
phases, and separates its torsion obstruction from positivity and branch
admissibility.

For a nonempty word, $`D\ge2`$, positive exponents $`a_i`$, and
$`\gcd(q_i,D)=1`$, the phase matrix has zero kernel and cyclic cokernel.
The weighted offset class vanishes exactly when the rational phase solution
is integral. These are integer-lattice statements; the
[field cochain modules](README.md) use a different coefficient category.

## Integral cyclic transport

Let $`r\ge1`$, $`D\ge2`$, $`a_i\ge1`$, and

```math

(Mx)_i=D^{a_i}x_{i+1}-q_i x_i,\qquad x_r=x_0,

```

with $`\gcd(q_i,D)=1`$. Put

```math

Q=\prod_iq_i,\quad K=\sum_i a_i,\quad
\Delta=D^K-Q,\quad
w_i=D^{s_i}\prod_{j>i}q_j.

```


Since $`Q`$ is coprime to $`D`$, $`D^K=Q`$ is impossible; hence $`\Delta\ne0`$. Also

```math

\gcd(D,\Delta)=1,\qquad \gcd(q_i,\Delta)=1.

```

Indeed, a prime dividing both $`q_i`$ and $`\Delta`$ would divide $`Q`$ and therefore $`D^K`$, contradicting $`\gcd(q_i,D)=1`$.

Weighted summation cancels all intermediate coordinates:

```math

\sum_iw_i(Mx)_i=\Delta x_0.

```

The two cyclic determinant terms give

```math

\det M=(-1)^{r-1}\Delta.

```

For $`r=1`$, the single entry is $`D^{a_0}-q_0`$, agreeing with this formula.

Here is direct **integral recovery**, without treating rational scaling as unimodular. Given integer $`c_i`$, solve the phase recurrence over $`\mathbb Q`$, starting at

```math

x_0=\frac{\sum_iw_ic_i}{\Delta}.

```

Composition gives endpoint closure. If $`\theta(c)=0`$, this $`x_0`$ is integral. For $`1\le i<r`$, prefix and suffix composition give integer offsets $`A_i,B_i`$ with

```math

D^{s_i}x_i=\Bigl(\prod_{j<i}q_j\Bigr)x_0+A_i\in\mathbb Z,

```


```math

\Bigl(\prod_{j\ge i}q_j\Bigr)x_i=D^{K-s_i}x_0-B_i\in\mathbb Z.

```

The two coefficients of $`x_i`$ are coprime. Bézout therefore implies $`x_i\in\mathbb Z`$.

Consequently $`\ker\theta=M\mathbb Z^r`$. The coefficient $`w_0=\prod_{j>0}q_j`$ is a unit modulo $`\vert\Delta\vert`$, so $`\theta`$ is onto. Thus

```math

\mathbb Z^r/M\mathbb Z^r\cong\mathbb Z/|\Delta|\mathbb Z.

```

The homogeneous recurrence and $`\Delta x_0=0`$ prove $`\ker M=0`$; rational solutions are unique.

Taking all $`q_i=q`$ gives the constant-multiplier case. The exact sequence is

```math

0\longrightarrow\mathbb Z^r\xrightarrow{M}
\mathbb Z^r\xrightarrow{\theta}\mathbb Z/|\Delta|\mathbb Z
\longrightarrow0.

```


The cyclic cokernel yields Smith form
$`\operatorname{diag}(1,\ldots,1,\vert\Delta\vert)`$. Alternatively, for $`r\ge2`$, two $`(r-1)`$-minors are, up to sign,

```math

\prod_{i=0}^{r-2}q_i,\qquad D^{s_{r-1}},

```

which are coprime. The general Smith-normal-form theorem is the standard algebraic dependency for this final terminology; the quotient calculation itself was proved directly.

**Kernel example:** $`r=1,q=3,D=2,c=1,a=(1)`$. Then

```math

\Delta=-1,\qquad M=[-1],\qquad M\iota(1)=-1\ne0.

```

The asserted sequence is not even a complex at that composition.

**Integer-scaling failure:** For $`r=2,q=3,D=2,a=(1,1)`$, the claimed coordinate change includes $`x_1=(3/2)y_1`$, not an integer-lattice automorphism. Moreover $`x_r=x_0`$ becomes

```math

y_r=(D^K/q^r)y_0,

```

not ordinary periodicity unless $`\Delta=0`$. The actual matrix

```math

\begin{pmatrix}-3&2\\2&-3\end{pmatrix}

```

has one-dimensional minors $`2,-3`$, not a minor equal to $`1`$. Their gcd is $`1`$, which supplies the correct argument.

**Coprimality negative control:** If the hybrid coprimality condition is removed, $`D=2,a=(1,1),q=(2,4)`$ gives

```math

M=\begin{pmatrix}-2&2\\2&-4\end{pmatrix},\qquad \Delta=-4.

```

Its Smith factors are $`2,2`$, not $`1,4`$. For $`c=(1,0)`$, the displayed weighted obstruction vanishes modulo $`4`$, but the rational solution is $`(-1,-1/2)`$. The coprimality hypotheses exclude this failure.

## Classical exact-valuation recovery

For classical positive exponents, every rotated numerator $`B_i`$ is odd and positive, and

```math

2^{a_i}B_{i+1}=3B_i+\Delta.

```

Because $`\Delta`$ is odd, $`\Delta\mid B_0`$ propagates to every $`B_i`$. With $`\Delta>0`$, define $`x_i=B_i/\Delta`$. These are positive odd integers and satisfy

```math

3x_i+1=2^{a_i}x_{i+1}.

```

Oddness of $`x_{i+1}`$ proves

```math

v_2(3x_i+1)=a_i.

```

This closes the recovery bridge; it is not merely rational fixed-point existence.

For the source’s witness,

```math

K=11,\quad \Delta=2048-243=1805,\quad
B=81+54+36+48+256=475.

```

At $`19`$, $`v_{19}(\Delta)=2>1=v_{19}(B)`$, so closure fails already. This is a useful **prime-power divisibility obstruction**, not failure of exact 2-adic letters after closure.

## Offset conductor and positive recovery

Under the corrected quotient isomorphism, $`[\mathbf1]`$ maps to $`N`$, so

```math

\operatorname{ord}[\mathbf1]
=L=\frac{|\Delta|}{\gcd(|\Delta|,N)}.

```

Therefore

```math

[c\mathbf1]=0\iff L\mid c.

```

The full-offset conductor is instead

```math

\operatorname{ord}[c\mathbf1]
=\frac{L}{\gcd(L,|c|)}
=\frac{|\Delta|}{\gcd(|\Delta|,cN)}.

```

Thus $`L`$ must be named the **unscaled conductor** if Definition 2.7 uses the full affine offset.

**One-phase counterexample to $`L=1`$:**

```math

q=1,\quad D=2,\quad c=3,\quad a=(2).

```

Here $`\Delta=3,N=1,L=3`$, but $`x=1`$ is an exact positive accelerated fixed point:

```math

(1+3)/4=1.

```

If a multiplier $`q\ge2`$ is desired, $`q=3,D=2,c=5,a=(3)`$ gives $`\Delta=L=5`$ and the exact fixed point $`(3+5)/8=1`$.

For $`q>0,D\ge2,c>0`$, all rotated $`N_i`$ are positive. Consequently positive closure is equivalent to

```math

\Delta>0,\qquad L\mid c.

```

When additionally $`D\nmid c`$, an integral phase cannot satisfy $`D\mid x_i`$, because its row equation modulo $`D`$ would force $`D\mid c`$. Each output phase is therefore $`D`$-free, giving exactly $`a_i`$ whole-base divisions and legal subsequent affine branches.

These positivity assumptions cannot be silently extended to signed multipliers. For example,

```math

q=-3,\quad D=2,\quad c=5,\quad a=(1)

```

has the positive fixed point $`1`$, whereas the repeated presentation $`a=(1,1)`$ has $`\Delta=4-9=-5`$.

The hybrid theorem imposes no branch partition. For example, $`D=2,q_0=1,a_0=1,c_0=2`$ has the integral positive solution $`x_0=2`$, but the raw map divides $`2`$ rather than taking its prescribed affine branch. The hybrid **lattice theorem remains correct**; an admissible-orbit theorem needs additional guards.

## 2-adic fixed points and exact periods

The two inverse shortcut branches on $`\mathbb Z_2`$ are

```math

h_0(y)=2y,\qquad h_1(y)=(2y-1)/3.

```

They land in the even and odd classes respectively. Every length-$`n`$ binary word defines a composed inverse branch whose linear coefficient is $`2^n/3^r`$. Its fixed-point equation has a unique solution because $`3^r-2^n`$ is odd. Following the inverse branches verifies every parity guard. Distinct words have distinct length-$`n`$ itineraries, and every fixed point of $`S^n`$ supplies one such word. Hence

```math

F_n:=\#\operatorname{Fix}(S^n)=2^n,\qquad n\ge1.

```

As a formal power series,

```math

\exp\!\left(\sum_{n\ge1}\frac{F_nz^n}{n}\right)=\frac1{1-2z}.

```


The exact-period point count is

```math

E_n=\sum_{d\mid n}\mu(n/d)\,2^d,

```

and the exact-period orbit count is $`E_n/n`$. In particular, $`F_2=4`$ but $`E_2=2`$.

The union $`\bigcup_{n\ge1}\operatorname{Fix}(S^n)`$ is countable and infinite. Already $`n=1`$ has exactly the two ordinary-integer fixed points $`0,-1`$. Thus the fixed counts and zeta function are compatible with countably many periodic points, not a continuum of them.

## Rational product formula and finite-place information

For nonzero rational $`\lambda`$,

```math

|\lambda|_\infty\prod_{p\text{ prime}}|\lambda|_p=1.

```

For $`\lambda=D^K/q^r`$, only primes dividing $`Dq`$ contribute. If $`D,q`$ are coprime, the source may define aggregate notation

```math

|\lambda|_D:=\prod_{p\mid D}|\lambda|_p,\qquad
|\lambda|_q:=\prod_{p\mid q}|\lambda|_p.

```

Composite numbers themselves are not prime places. For example $`D=4,q=9,K=r=1`$ uses the genuine places $`2,3`$:

```math

(1/4)\cdot9\cdot(4/9)=1.

```

If aggregate supports overlap, they must not be counted twice. For $`D=2,q=4,K=r=1`$, the doubly counted product would be $`2\cdot2\cdot(1/2)=2`$, not $`1`$.

**Exact counterexample to the universal finite-place no-go:** In the coprime raw family

```math

(q,c,D)=(2,1,3),

```

the seed $`1`$ has the positive cycle $`1\to3\to1`$. In contrast, residue $`2\bmod3`$ is invariant under the affine branch:

```math

2(2)+1\equiv2\pmod3.

```

Thus seed $`2`$ never divides and has

```math

F^j(2)=3\cdot2^j-1\longrightarrow\infty.

```

A finite residue certificate separates this divergent class from the displayed cycle. This does not solve classical Collatz; it refutes the generalized assertion actually stated.

Even at fixed classical multiplier data, $`a=(2,2)`$ and $`a=(1,3)`$ share $`\Delta=7`$ and the same drift, but their numerators are $`7`$ and $`5`$. The first closes at $`1`$; the second fails the obstruction at prime $`7`$. Drift sign alone does not certify an integral cycle.

## Mark-preserving prefix maps

For an extension $`w`$ of prefix $`w'`$, the proposed map

```math

\mathbb Z/m_w\mathbb Z\longrightarrow\mathbb Z/m_{w'}\mathbb Z,
\qquad [x]\longmapsto[x]

```

is well-defined exactly when

```math

m_{w'}\mid m_w.

```

For $`w'=11,w=110`$, the moduli are $`5,1`$. The map fails because $`5\nmid1`$, **not** because $`1\nmid5`$.

This is a valid small counterexample to generator-preserving natural reduction maps on all prefix edges. It does not exclude other bonding maps. Assigning zero maps to every strict extension and identity maps to equal nodes satisfies inverse-system composition, since compositions of strict zero maps remain zero.

The weakest correction is a no-go for the **specified marked reduction-map construction**. Any stronger theorem must specify the permissible systems and prove that they cannot retain enough information for the desired arithmetic recovery. The marked reduction obstruction does not supply such a universal theorem.

## Sources and formal interfaces

Related formulations appear in `/home/dell/collatz/FINALEE.MD`,
sections 7.14–7.14e and 9.14-hybrid. The arguments above retain the valid
integer assertions and give explicit counterexamples to stronger statements.

[Conductors.lean](../Foundations.Main.StartHere/lean/Conductors.lean) proves
the scalar conductor criterion.
[ThreeAffineLegal.lean](../QCD.ThreeAffineClosure.001/lean/ThreeAffineLegal.lean)
formalizes exact positive odd recovery for three letters.
[ComplexLocalSystem.lean](lean/ComplexLocalSystem.lean) formalizes actual
twisted quotients over fields. The general integral hybrid cokernel proof
on this page is a written proof, not that field theorem.
