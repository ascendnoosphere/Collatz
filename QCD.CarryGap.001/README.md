# Carry gap

Let $`q`$ and $`c`$ be odd positive integers. For a bit $`e\in\{0,1\}`$ set
```math
F_0(x)=\frac{x}{2},\qquad F_1(x)=\frac{qx+c}{2}.
```
Let $`w=(e_0,\ldots,e_{m-1})`$ be a word in which the bit $`1`$ occurs $`r`$ times, and assume $`q^r<2^m`$. Starting from $`(P,B)=(1,0)`$ on the empty word, a first bit $`e`$ followed by data $`(P',B')`$ produces $`(P',2B')`$ when $`e=0`$ and $`(qP',P'+2B')`$ when $`e=1`$. Write $`(P,B)`$ for the data of $`w`$. The fixed point and its phases are
```math
\xi_0=\frac{cB}{2^m-P},\qquad \xi_{i+1}=F_{e_i}(\xi_i).
```
Let $`n_i`$ be the positive integer of parity $`e_i`$ nearest to $`\xi_i`$, choosing the smaller integer when the distances are equal. The carry energy is
```math
E(w)=\max_{0\le i<m}\lvert\xi_i-n_i\rvert.
```
Either $`E(w)=0`$ or $`E(w)>1/2`$. The energy is zero if and only if every phase $`\xi_i`$ is a positive integer of parity $`e_i`$.

For $`q=3`$ and $`c=1`$, the word $`10`$ has phases $`1,2`$ and energy $`0`$. The word $`100`$ has phases $`1/5,4/5,2/5`$, nearest integers $`1,2,2`$, and energy $`8/5`$.

This does not assert that the classical Collatz map reaches $`1`$. Zero energy is not excluded. No claim is made that energies arbitrarily close to $`1/2`$ occur for $`c=1`$, and the gap is not asserted when $`q^r<2^m`$ fails.
