<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Five displayed solutions of \(x^{2}+7=2^{n}\)

Let \(\mathbb{N}\) be the nonnegative integers. For \(x,n\in\mathbb{N}\), the equation \(E(x,n)\) is \(x^{2}+7=2^{n}\). With \(n\) fixed, this says that \(x\) is a root of the polynomial \(X^{2}+7-2^{n}\).

## Statements

The powers \(2^{3}=8\), \(2^{4}=16\), \(2^{5}=32\), \(2^{6}=64\), \(2^{7}=128\), and \(2^{15}=32768\) follow from \(2^{k+1}=2^{k}\cdot 2\), together with \(2^{10}=2^{5}\cdot 2^{5}=1024\).

The squares are \(1^{2}=1\), \(3^{2}=9\), \(5^{2}=25\), \(11^{2}=121\), and \(181^{2}=32761\). The last two use \(11=10+1\) and \(181=180+1\), and \(180\cdot 180=324\cdot 100=32400\).

Therefore \(1^{2}+7=2^{3}\), \(3^{2}+7=2^{4}\), \(5^{2}+7=2^{5}\), \(11^{2}+7=2^{7}\), and \(181^{2}+7=2^{15}\).
The five displayed pairs are \((1,3)\), \((3,4)\), \((5,5)\), \((11,7)\), and \((181,15)\).

## Reduction record

**ORIGINAL OBLIGATION.** Prove \(E(x,n)\) at each of the five displayed pairs \((1,3)\), \((3,4)\), \((5,5)\), \((11,7)\), and \((181,15)\).

**REPLACEMENT OBLIGATIONS.** Evaluate \(2^{3}\), \(2^{4}\), \(2^{5}\), \(2^{6}\), \(2^{7}\), and \(2^{15}\) from the recurrence \(2^{k+1}=2^{k}\cdot 2\) and the splits \(10=5+5\) and \(15=10+5\). Evaluate the five squares, expanding \(11=10+1\) and \(181=180+1\) with \(180=18\cdot 10\). Add \(7\) and compare with the matching power of two.

**RECOVERY ARGUMENT.** Substituting each evaluated square and each evaluated power into the two sides of \(E(x,n)\) returns exactly that displayed pair. Every displayed pair is recovered, and no displayed pair is omitted. No further pair is obtained.

**DIFFICULTY DECREASE.** The obligation is five closed comparisons. Every power of two on the list reduces to the value \(2\) by a fixed number of doublings, and each square splits into products of integers at most \(180\). There is no search over exponents and no descent on a general discriminant.

**PRESERVATION CONDITIONS.** The equation remains \(x^{2}+7=2^{n}\) in \(\mathbb{N}\), and the five pairs remain exactly the displayed list. The identities are equalities, not congruences. No bound on a general exponent, no coprimality restriction, and no parity restriction is added. Positivity of the five inputs is unchanged.

## What is not claimed

It is not proved that every positive solution of \(x^{2}+7=2^{n}\) equals one of the five displayed pairs.

It is not proved that an odd positive integer \(D\) has at most one representation \(x^{2}+D=2^{n}\), and it is not proved that \(D=7\) is exceptional for that count.

Satisfaction of \(E(x,n)\) is not a cycle, not a congruence \(2^{a}\equiv -x\pmod{7}\), and not a positivity window.

A finite grid of further pairs, including pairs that fail \(E(x,n)\), is not a classification of the positive solutions.
