# Logarithmic gap of one eight-step block

Let $\log$ denote the natural logarithm. Then
$$
\log\frac{256}{243}=8\log 2-5\log 3.
$$
Equivalently,
$$
\frac18\log\frac{256}{243}=\log 2-\frac58\log 3.
$$
The common value is positive because $243<256$.

Let $r_0,\ldots,r_7$ be positive real numbers and let $P=\prod_{i=0}^{7} r_i$. The block lies below $1$ by at least this gap when
$$
-\log P\ge\log\frac{256}{243}.
$$
That inequality forces $P\le 243/256$, and therefore $P<1$. A strict deficit forces the strict bound $P<243/256$.

The same product bound holds if every factor satisfies
$$
\log r_i\le -\frac18\log\frac{256}{243},
$$
equivalently $\log r_i\le (5/8)\log 3-\log 2$. Each such factor is strictly less than $1$. The constant $243/256$ is optimal: the block with first factor $243/256$ and the other seven factors equal to $1$ is positive, has product $243/256$, and has logarithmic deficit exactly $\log(256/243)$.

Not claimed. The deficit hypothesis is an assumption on eight positive real factors. It is not a property proved here for the branches of the classical Collatz map, and it does not imply that iteration of that map reaches $1$.
