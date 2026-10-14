<!-- SPDX-License-Identifier: CC-BY-4.0 -->

# Denominator budgets for ascending inverse words

Let $q,c,D$ be positive integers with $D\ge2$, and use the raw map

```math
F(n)=\begin{cases}n/D,&D\mid n,\\ qn+c,&D\nmid n.\end{cases}
```

A word is a finite sequence of affine and division letters. It is **legal**
when each letter agrees with the branch selected by its input. Write $s(w)$
for its affine count and $e(w)$ for its division count.

## Necessary bound and unique reconstruction

If a legal word sends $p$ to $m$ with $1\le p<m$, then

```math
D^{e(w)}<(q+c)^{s(w)}.
```

The strict inequality follows from the stronger estimate

```math
D^{e(w)}m\le p(q+c)^{s(w)}.
```

For a fixed word, its exact offset $B(w)$ gives

```math
q^{s(w)}p=D^{e(w)}m-cB(w).
```

Since $q^{s(w)}>0$, there is at most one legal start for that word and
terminal value. Divisibility of the right-hand side determines a candidate;
replaying the word checks positivity, every branch, and the endpoint.
The offset recursions and this reconstruction are proved in
[`OffsetFormula`, `SolvedStart`, and `UniquePreimage`](lean/InverseBudget.lean).

## A finite search at fixed affine depth

For each pair $s,e\ge0$, the recursive list `Words s e` contains exactly the
words of those counts, with no duplicates. Its length is

```math
\binom{s+e}{s}.
```

If the affine count is at most a fixed $S\ge1$, define $E$ by

```math
D^E<(q+c)^S\le D^{E+1}.
```

Every ascending word has $1\le s\le S$ and $0\le e\le E$. Enumerating these
finitely many lists and testing their reconstructed starts therefore finds
all ascending preimages at that affine depth. The cutoff can be computed
with integer multiplication; no floating-point logarithm is required.
The proof also supplies the coarser bound $e<(q+c)^S$.

For $(q,c,D,m,S)=(3,1,2,8,3)$, the positive starts below $8$ are exactly
$3,5,6$. Their raw paths are

- $5\to16\to8$;
- $3\to10\to5\to16\to8$;
- $6\to3\to10\to5\to16\to8$.

A pure division tower starts at $D^em\ge m$ and hence cannot be an ascending
preimage. The bound concerns a fixed affine ceiling; allowing that ceiling
to grow is a different search problem.

## Proofs and implementation

- [Detailed proofs](tex/InverseBudget.tex).
- [Lean definitions, counting, reconstruction and budget theorems](lean/InverseBudget.lean).
- [Overflow-checked inverse search](go/InverseBudget.go).
- [Word counts, forward/inverse comparisons and boundary tests](go/InverseBudget_test.go).

The Go word solver supports lengths through $16$. Its inverse search supports
an affine ceiling from $1$ through $16$ and stores at most $64$ distinct
starts. Arithmetic overflow or exhausted storage returns an unsuccessful
status, not a purported complete list. A successful search covers the
specified ceiling only.

The tests enumerate every binary word through length $16$, compare inverse
and forward counts for $2\le D\le4$, $1\le q,c\le4$, $2\le m\le12$,
$1\le S\le3$, and check malformed words, strict-budget boundaries,
integer overflow, and allocation-free inverse traversal.

Run from the repository root:

```sh
make lean
make go GOFILE=QCD.InverseBudget.001/go/InverseBudget.go
CGO_ENABLED=0 "$HOME/.local/go/bin/go" test ./QCD.InverseBudget.001/go
make tex TEXFILE=QCD.InverseBudget.001/tex/InverseBudget.tex
bash Scripts/CheckIgnoredPdfs.sh
bash Scripts/CheckIgnoredTexTemps.sh
```
