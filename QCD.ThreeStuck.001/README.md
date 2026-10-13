# Inverse odd steps keep a budget of factors of 3

Let $z$ be a natural number, and write $v_3(z+1)$ for the exponent of $3$ in $z+1$. The inverse odd step is
$$
I(z)=\frac{2z-1}{3}.
$$
Whenever $3$ divides $z+1$, the numerator $2z-1$ is divisible by $3$, so the quotient is exact and
$$
I(z)+1=\frac{2(z+1)}{3}.
$$
The numerator $2z+1$ is not divisible by $3$ in that case, so the opposite sign is not an inverse odd step.

Let $b=v_3(z+1)$. For every natural number $k\le b$, the $k$-fold iterate satisfies
$$
I^k(z)+1=\frac{2^k(z+1)}{3^k},\qquad v_3(I^k(z)+1)=b-k.
$$
Thus $3$ divides $I^k(z)+1$ if and only if $k<b$. Fewer than $b$ inverse odd steps leave a factor of $3$ in the image plus one. Exactly $b$ inverse odd steps remove every such factor. Each of those $b$ steps is exact division by $3$.

In particular $I(2)=1$. Here $v_3(2+1)=1$, so one step removes the only factor, and $3$ does not divide $2$. The seed $8$ has $v_3(9)=2$, with images $8\mapsto 5\mapsto 3$: one step leaves the factor in $5+1$, and the second step removes it.

This does not say that iteration of the classical Collatz map reaches $1$. It does not treat the even inverse branch $z\mapsto 2z$, and it does not assert a global descent.
