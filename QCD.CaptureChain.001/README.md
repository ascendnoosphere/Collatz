<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Capture by a decreasing chain of legal joins

Let $`q`$, $`c`$, and $`D`$ be integers with $`|D|\ge 2`$. The raw map $`C`$ on the integers is
```math
C(n)=\begin{cases}
n/D & \text{if }D\mid n,\\ qn+c & \text{otherwise.}
\end{cases}
```
The quotient in the first branch is the integer quotient. A legal join from $`n`$ to a parent $`m`$ is a positive integer $`k`$ such that $`C^{k}(n)=m`$.

Let $`m_0,\ldots,m_t`$ be integers with $`m_t=1`$. Suppose that for every $`i<t`$ there is a legal join from $`m_i`$ to $`m_{i+1}`$ and $`|m_{i+1}|<|m_i|`$. Then some natural number $`N`$, including the possibility $`N=0`$, satisfies $`C^{N}(m_0)=1`$. The number of states is at most $`|m_0|`$. If $`t=0`$, then $`m_0=1`$ and $`N=0`$ is such a time. If $`t\ge 1`$, then $`N`$ may be taken positive and $`|m_1|<|m_0|`$.

The proof is induction on $`t`$. The inductive step adds the length of the given join from $`m_0`$ to $`m_1`$ to a time already obtained for $`m_1`$. It does not search the orbit of $`m_0`$.

For $`q=3`$, $`c=1`$, and $`D=2`$, the one-state chain $`1`$ is certified at time $`0`$. The chain $`2,1`$ is a legal join because $`C(2)=1`$ and $`|1|<|2|`$, so the raw orbit of $`2`$ reaches $`1`$. These two chains do not imply the same conclusion for an arbitrary integer.

Nothing here asserts that a decreasing chain ending at $`1`$ exists for every integer, or for every positive integer. A legal join to a strictly smaller parent, without a continuation of the chain to $`1`$, does not certify that the orbit reaches $`1`$. In particular, it is not claimed that the classical raw map sends every positive integer to $`1`$.
