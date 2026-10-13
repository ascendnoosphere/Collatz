<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Sign of the mirror quotient

Let $n$ be an integer and let $v$ be a nonnegative integer. The mirror quotient is $(3n-1)/2^{v}$. A finite schedule is a list of such exponents. Its states are $x_{0}=n$ and
$$
x_{j+1}=\frac{3x_{j}-1}{2^{v_{j}}},
$$
formed when $x_{j}$ is an integer and $2^{v_{j}}$ divides $3x_{j}-1$. The schedule is integral when every state through the last step is an integer.

If $n>0$ and $2^{v}$ divides $3n-1$, then $(3n-1)/2^{v}$ is a positive integer. If $n<0$ and the schedule is integral, then every state is a negative integer. The same integrality hypothesis with a positive seed keeps every state positive.

The exponent $1$ fixes $1$. The exponents $1$ and $2$ exchange $5$ and $7$. Both are positive cycles of this quotient. The exponent $3$ at the seed $1$ is not integral, since $8$ does not divide $2$.

These statements do not concern the numerator $3n+1$. They do not say that every positive integer reaches $1$. They do not list every positive cycle. They do not assign a sign to a schedule that fails to be integral: the rational steps with exponents $3$ and $0$, started at $1$, pass through $1/4$ and then $-1/4$.
