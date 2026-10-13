<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# One division at a first hit

Let $q,c,d,n\in\mathbb{Z}$ with $|d|\ge 2$, and let the raw step be
$$
T(m)=\begin{cases} m/d, & d\mid m,\\ qm+c, & d\nmid m.\end{cases}
$$
Write $T^{0}(n)=n$ and $T^{j+1}(n)=T(T^{j}(n))$. Whenever $d$ divides $m$, the symbol $m/d$ denotes the unique integer satisfying $m=(m/d)\,d$. The offset sum is $U_{0}(q)=0$ and $U_{j+1}(q)=U_{j}(q)+q^{j}$, and it satisfies $U_{j+1}(q)=q\,U_{j}(q)+1$. The affine state is
$$
A_{j}(q,c,n)=q^{j}n+c\,U_{j}(q).
$$
Time $j$ is a first hit of $n$ when $d\mid A_{j}(q,c,n)$ and $d\nmid A_{i}(q,c,n)$ for every natural number $i<j$.

For every parameter record, every integer seed and every time $j$, the raw prefix guard and the affine prefix guard agree: $d$ divides no raw iterate $T^{i}(n)$ with $i<j$ if and only if $d$ divides no affine state $A_{i}(n)$ with $i<j$. Consequently an earlier affine hit is an earlier raw hit, and an earlier raw hit is an earlier affine hit.

If the raw guard holds, then $T^{j}(n)=A_{j}(n)$. The proof is induction on $j$. The successor evaluates the affine branch at the one earlier time $j$, substitutes the inductive equality, and applies $U_{j+1}(q)=q\,U_{j}(q)+1$.

If $j$ is a first hit, the affine guard and the equivalence give the raw guard, so the prefix theorem yields $T^{j}(n)=A_{j}(n)$. Divisibility of that common value selects the division branch once:
$$
T^{j+1}(n)=A_{j}(n)/d.
$$
This quotient may still be divisible by $d$. The step does not divide out the full power of $d$ present in $A_{j}(n)$.

## Reduction record

**ORIGINAL OBLIGATION.** For every parameter record, every integer seed and every time $j$, assuming $j$ is the first time $d$ divides the affine state, prove that the raw iterate at time $j$ equals that affine state and that the next raw step equals the affine state divided once by $d$.

**REPLACEMENT OBLIGATIONS.** (i) Prove again that a raw prefix with no division before time $j$ equals the affine state at time $j$. (ii) Prove by a second induction on $j$ that the raw prefix guard and the affine prefix guard are equivalent, using the prefix theorem only at strictly smaller times. (iii) From a first affine hit, transfer the guard to the raw prefix, apply the prefix theorem, and evaluate one division branch.

**RECOVERY ARGUMENT.** Both displayed values are states of the original raw step at the original seed. The state at time $j$ is recovered by the prefix theorem once the second induction has replaced the affine guard by the raw guard. The state at time $j+1$ is the definition of the raw step on a divisible integer, hence the exact quotient by $d$. Equality of the two representations of the state at time $j$ transports that quotient. The argument stops at this one division: it does not iterate the branch, does not continue the orbit, and does not invent a return time for a seed whose affine states are never divisible.

**DIFFICULTY DECREASE.** The obstruction is that the first-hit guard is stated on affine states, while the closed prefix formula takes its hypothesis on raw states, and that the next raw branch is a division rather than another affine step. The first induction removes the closed-form gap along one division-free raw prefix; its measure is the time, which falls to the base $j=0$ in every branch. The second induction removes the mismatch of the two guards. At a successor it consults the equivalence only at time $j$ and the prefix theorem only at that same smaller time, then compares one divisibility. The division clause is a single conditional on a state already known to be divisible. No valuation, no contraction factor and no search over later times remains.

**PRESERVATION CONDITIONS.** The parameter record is unchanged: $q$ and $c$ are arbitrary integers and $|d|\ge 2$, so negative multipliers, offsets, divisors and seeds remain. The quantifiers are every record, every seed and every time, including a first hit at time zero. Equality is identity of integers. The quotient is the unique integer $q_{0}$ with $A_{j}(n)=q_{0}\,d$, not a truncation of a non-divisible integer and not the quotient by a higher power of $d$.

## What is not claimed

- A value of $T^{m}(n)$ for any $m>j+1$, or an identification of any later state with an affine state.
- That some time is a first hit for every seed. Seeds whose affine states are never divisible are not given a return.
- Removal of every factor of $d$. If $d^{2}$ divides $A_{j}(n)$, the next state may still be divisible by $d$.
- A contraction, a bound on absolute values, or a comparison of $|T^{j+1}(n)|$ with $|T^{j}(n)|$.
- A block decomposition, a residue-dependent exponent, or a total return map on trapped seeds.
- Any density of seeds, times or residues.
- Convergence, divergence or cycle structure of any classical Collatz orbit.
- That agreement on a finite grid of coefficients, divisors, seeds and times proves the identities for integers outside that grid.
