<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Antipodal Hamming gap and balanced cyclic cuts

For a binary word $w$ of length $2h$, let $N(w)$ be its number of ones and let
$H(w)$ be the Hamming distance between its two halves of length $h$. A **transport**
is a cyclic cut whose two halves have the same number of ones and differ at
exactly two positions. One mismatch is $1$ against $0$ and the other is $0$
against $1$. The positions need not be adjacent.

## Exact classification

For every word of even length, including the empty word:

- Every cyclic cut has the same antipodal distance $H(w)$.
- $H(w)$ and $N(w)$ have the same parity.
- $H(w)=0$ exactly when $w=uu$ for a word $u$.
- $H(w)=2$ exactly when a transport exists. A witnessing cut can be chosen
  within the first $h$ rotations.

Consequently, if $N(w)$ is even, $w$ is not a doubled block, and no transport
exists, then

```math
H(w)\ge4.
```

This is a binary-word theorem. Applying it to a cycle requires proving the
transport exclusion. The adjacent-swap exclusion in
[QCD.OneBit.001](../QCD.OneBit.001/README.md) covers a narrower class of words.

## Constructing the cut

Suppose $N(w)=2t$. Let $f(k)$ count ones in a window of length $h$ starting
at position $k$. For $0\le k<h$,

```math
f(k+1)=f(k)-w_k+w_{k+h},\qquad f(h)=2t-f(0).
```

Successive counts differ by at most one, and $t$ lies between the two endpoint
counts. Sliding the window therefore finds the first cut with $f(k)=t$ after
at most $h$ updates. For the empty word the cut is zero. Initial counting and
the window search use a linear number of bit inspections.

When $H(w)=2$, this cut is a transport: rotation preserves the distance, and
the equal counts force one mismatch in each direction.

## Sharpness and boundary cases

| Word | $N(w)$ | $H(w)$ | Role |
| --- | ---: | ---: | --- |
| `000011101000` | 4 | 4 | Attains the bound and satisfies all three hypotheses |
| `10` | 1 | 1 | Shows why the total count must be even |
| `0101` | 2 | 0 | Shows why doubled blocks must be excluded |
| `0011` | 2 | 2 | Shows why transports must be excluded |
| `001100` | 2 | 2 | Its halves `001` and `100` move nonadjacent positions |

These are word examples; no cycle realization is assumed.

## Proofs and exact checks

- [Written proof](tex/HammingGap.tex): rotation invariance, the unit-step
  intermediate-value argument, the two classifications and the sharp bound.
- [Lean proof](lean/HammingGap.lean): the same statements, the bounded transport
  witness and the displayed word examples. The module is in the default build.
- [Go checker](go/HammingGap.go) and [tests](go/HammingGap_test.go): a packed-word
  balanced-cut algorithm and an independent census of every cyclic cut.

The checker accepts precisely even lengths from zero through $20$, with no
bits outside the declared length. It exhaustively checks all $1{,}398{,}101$
words at half-lengths zero through ten, including the empty word. At length
$20$, exactly $477{,}184$ words satisfy the gap hypotheses. These finite counts
are computational results; the general classification is proved separately.
Successful single-word checks allocate no memory. Malformed masks, odd lengths
and larger budgets are rejected before the rotation or enumeration loops.

Run from the repository root:

```sh
make lean
make go GOFILE=QCD.HammingGap.001/go/HammingGap.go
CGO_ENABLED=0 go test ./QCD.HammingGap.001/go
make tex TEXFILE=QCD.HammingGap.001/tex/HammingGap.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
