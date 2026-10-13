# Inverse odd root

Let $z$ be an integer with $z+1\neq 0$. Write $b=v_3(z+1)$ and let $m$ be the integer $(z+1)/3^b$. Then $3\nmid m$. The inverse odd root
$$
R=2^b m-1
$$
is an integer. Exactly $b$ steps of $I(n)=(2n-1)/3$ are integral, and $I^b(z)=R$. Consequently $3\nmid(R+1)$ and $3\nmid(2R-1)$, so the inverse odd step stops at $R$.

The odd branch $F(n)=(3n+1)/2$ returns from $R$ to $z$ in $b$ integral steps. For each $k<b$, the state $F^k(R)$ is odd.

If $0\leq z$, then $0\leq R\leq z$.

The step is $I(n)=(2n-1)/3$. For every integer $n$, the numerators $2n+1$ and $2n-1$ differ by $2$.

Not claimed. Three may divide $R$: $R(8)=3$. The comparison $R\leq z$ uses $0\leq z$: $R(-4)=-3>-4$. Nothing here asserts that iteration of the classical Collatz map reaches $1$.
