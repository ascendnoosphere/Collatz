<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Equal halves

Let $`q`$ be a natural number with $`q\equiv 1\pmod{2}`$, and let $`U`$ and $`V`$ be binary parity words of common length $`h`$ and common odd-step count $`r`$. The letter $`1`$ is one odd step. Write $`o(W)`$ for the number of odd letters in $`W`$, and write $`A(W)`$ for the unscaled numerator
```math
A(W)=\sum_{i:W_i=1} q^{o(W_{>i})}\,2^i.
```
Set $`Q=2^h-q^r`$ and $`M=2^h+q^r`$, and assume $`Q>0`$. The concatenation identity
```math
A(UV)=q^r A(U)+2^h A(V)
```
holds before either divisibility below. It rearranges as
```math
A(UV)-q^r\bigl(A(U)-A(V)\bigr)=M A(V)
```
and
```math
A(UV)=q^r\bigl(A(U)+A(V)\bigr)+Q A(V).
```
Consequently the closure denominator of the concatenation divides the numerator,
```math
2^{|UV|}-q^{o(UV)}\mid A(UV),
```
if and only if $`M`$ divides $`A(U)-A(V)`$ in the integers and $`Q`$ divides $`A(U)+A(V)`$. Under the equal-halves hypotheses that denominator is $`2^{2h}-q^{2r}=MQ`$.

Divisibility by $`M`$ of the difference does not imply divisibility by $`Q`$ of the sum. For $`q=3`$, $`U=000011`$, and $`V=101000`$, one has $`h=6`$, $`r=2`$, $`A(U)=80`$, $`A(V)=7`$, $`M=73`$ divides $`A(U)-A(V)`$, and $`Q=55`$ does not divide $`A(U)+A(V)`$. That word is not a numerator closure.

Equal odd-step counts are a hypothesis, not a conclusion. Vanishing of one factor is not a closure. No claim is made that the classical Collatz map sends a positive integer to $`1`$.
