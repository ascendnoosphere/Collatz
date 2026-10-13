# Carry energy of one block word

Let $b$ and $r$ be integers with $b\geq 1$ and $r\geq 1$. The parity word
$$
0^{b}1^{r}0^{b-1}101^{r-1}
$$
splits into the halves $0^{b}1^{r}$ and $0^{b-1}101^{r-1}$. Both halves have length $h=b+r$ and both contain $r$ odd letters. Off the indices $b-1$ and $b$, the halves carry the same letter. Those two indices are adjacent, and the halves swap $0,1$ there.

Let $\lambda=3^{r}/2^{h}$. The carry energy is the unique rational $E$ satisfying $1-\lambda E=E$. It is
$$
E=\frac{1}{1+\lambda}=\frac{2^{h}}{2^{h}+3^{r}}.
$$
Thus $E>1/2$ if and only if $3^{r}<2^{h}$. For $b\geq 1$ one has $E\neq 1/2$, because $2^{h}$ is even and $3^{r}$ is odd.

For each fixed $b\geq 1$, $E\to 0$ as $r\to\infty$. In particular the same sequence does not tend to $1/2$. Along sequences of exponents, the energy stays strictly above $1/2$ and tends to $1/2$ if and only if the ratio stays strictly below $1$ and tends to $1$.

The case $b=2$, $r=3$ gives $E=32/59$.

This does not assert that $E\to 1/2$ for fixed $b$. It does not produce a nearest positive integer of the prescribed parity, and it does not assert that the classical Collatz map reaches $1$.
