<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# A parent above the seed

Let $T$ send an even natural number $n$ to $n/2$ and an odd natural number $n$ to $(3n+1)/2$. For odd $n$, the value $3n+1$ is even, so the second branch is an integer.

The iterates $T^{0}(27),\ldots,T^{9}(27)$ are
$$
27,\ 41,\ 62,\ 31,\ 47,\ 71,\ 107,\ 161,\ 242,\ 121.
$$
The same orbit satisfies $T^{23}(27)=445$, $T^{24}(27)=668$, $T^{25}(27)=334$, and $T^{26}(27)=167$. The state at time $23$ is odd and the next two states are even. For every $t<24$, those two states are not both even.

The quotient $(445-1)/2$ equals $222$. Three applications of $T$ to $445$ equal two applications of $T$ to $222$, and both equal $167$. Since $222=2\cdot 111$ with $111$ odd, the first odd positive iterate of $222$ occurs after exactly one division by $2$.

The inverse odd step $(2y-1)/3$ is defined only when $y\equiv 2\pmod{3}$. It is not defined at $222$. The integer $222+1=223$ is not divisible by $3$, so the odd-chain ancestor of $222$ is $222$ itself, after zero divisions by $3$. One inverse odd step at $167$ returns $111$. The ancestor $222$ is strictly larger than $27$.

These statements do not assert that any iterate of $27$ equals $1$, and they do not assert that every positive integer reaches $1$.
