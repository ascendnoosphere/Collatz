<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# An odd burst from a string of ones

Let $`\mathbb{N}`$ contain $`0`$. Let $`T`$ send an even natural number $`n`$ to $`n/2`$ and an odd natural number $`n`$ to $`(3n+1)/2`$. If $`n`$ is odd, then $`3n+1`$ is even, so the second value is an integer.

For every $`a\in\mathbb{N}`$ and every $`k\le a`$,
```math
T^{k}(2^{a}-1)=3^{k}\cdot 2^{a-k}-1.
```
In particular, $`a`$ odd steps carry $`2^{a}-1`$ to $`3^{a}-1`$. Each input of those steps is odd. The integer $`3^{a}-1`$ is even. If $`a\ge 2`$, then $`3^{a}-1>2^{a}-1`$.

These statements do not assert that any iterate equals $`1`$, and they do not assert that every positive integer reaches $`1`$.
