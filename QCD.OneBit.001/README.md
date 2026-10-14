<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# Adjacent-swap exclusion for shortcut cycles

For the classical shortcut

$$
T(n)=
\begin{cases}
n/2,&n\text{ even},\\
(3n+1)/2,&n\text{ odd},
\end{cases}
$$

no closed orbit can have two consecutive halves that differ only by swapping
an adjacent even-odd pair. The prefix and suffix around the swapped pair may
be arbitrary finite words.

## Numerator identities

A word uses $0$ for an even branch and $1$ for an odd branch, in chronological
order. Write $\nu(w)$ for its number of ones. Define

$$
A(\varnothing)=0,\qquad
A(0w)=2A(w),\qquad
A(1w)=3^{\nu(w)}+2A(w).
$$

When the branches of $w$ agree with the parities of the successive states,

$$
2^{|w|}T^{|w|}(n)=3^{\nu(w)}n+A(w).
$$

For arbitrary finite words $p,s$, put

$$
L=p01s,\qquad R=p10s,\qquad
h=|p|+2+|s|,\qquad r=\nu(p)+1+\nu(s).
$$

Their lengths and odd counts agree. The exact numerator difference is

$$
A(L)-A(R)=2^{|p|}3^{\nu(s)}.
$$

With $M=2^h+3^r$ and $\mu=2^{|p|}3^{r+\nu(s)}$, concatenation gives

$$
A(LR)=MA(R)+\mu,\qquad A(RL)+\mu=MA(L).
$$

Here $h\ge2$, $r\ge1$ and $M\ge7$. The modulus is coprime to $2$ and $3$,
so it cannot divide the monomial $\mu$. Consequently neither $A(LR)$ nor
$A(RL)$ is divisible by $M$.

A return with either concatenated word would require

$$
(2^{2h}-3^{2r})n=A(w).
$$

The left side is divisible by $M$, by the difference-of-squares factorization.
This contradicts the numerator identities. The exclusion holds at every
natural starting state, not just below a search bound.

## Examples and scope

| Prefix $p$ | Suffix $s$ | $L$ | $R$ | $M$ | $\mu$ | $A(LR)$ | $A(RL)$ |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: |
| empty | empty | $01$ | $10$ | $7$ | $3$ | $10$ | $11$ |
| $1$ | $0$ | $1010$ | $1100$ | $25$ | $18$ | $143$ | $157$ |

The ordinary shortcut cycle $1\mapsto2\mapsto1$ has word $10$. Its doubled
word $1010$ also returns to $1$; it repeats a half instead of swapping the
adjacent pair between halves. This illustrates why the conclusion is an
exclusion for a specified word family, not a classification of all cycles or
a proof of capture.

The two-halves divisibility criterion is developed more generally in
[QCD.EqualHalves.001](../QCD.EqualHalves.001/README.md).

## Proofs and exact checks

- [Written proof](tex/OneBit.tex): the affine formula, transport identities,
  coprimality obstruction and examples.
- [Lean proof](lean/OneBit.lean): all word identities and return exclusions,
  with arbitrary prefixes and suffixes.
- [Go implementation](go/OneBit.go) and [tests](go/OneBit_test.go): exhaustive
  checks of the $(h-1)2^{h-2}$ pairs at each half-length $2\le h\le12$,
  totaling $20481$ pairs. Parity replay also checks the affine formula for
  $1024$ seeds at every word length from $0$ through $10$.

The Go coefficient budget is $24$ letters. Unsupported words are rejected;
odd-step replay rejects an overflowing numerator. The bounded checks test the
implementation, while the universal exclusion is proved in the written and
Lean arguments.

```sh
lake build OneBit
make go GOFILE=QCD.OneBit.001/go/OneBit.go
CGO_ENABLED=0 go test ./QCD.OneBit.001/go
make tex TEXFILE=QCD.OneBit.001/tex/OneBit.tex
```
