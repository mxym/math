# Sharp period 1122 at the norm-six threshold in Z[sqrt(-2)]

Research note, 8 October 2026. [Complete theorems and rigorous written
proof](paper.md) · [independent exact checker](code/check_exact.py) ·
[lower-period witness file](code/lower_cycles.json.gz) ·
[full successful quotient partition](code/positive_q1122.json.gz) ·
[exceptional-prime closure](code/exceptional_closure.json) ·
[verification log](results/replay.txt) · [scope audit](AUDIT.md).

## Theorem scope

For `t=sqrt(-2)`, consider the fourteen actual Euclidean lattice
steps of squared norm at most 6. They are exactly the permissible
steps at **every** real radius `sqrt(6) <= D < sqrt(8)`.

We prove that the **least scalar period of any successful finite
principal-ideal sieve** (with arbitrary nonzero nonunit, possibly
composite, generators) is

\[
\boxed{Q_{\min}=1122=2\cdot3\cdot11\cdot17.}
\]

A successful sieve uses the seven generators
`t, 1+t, 1-t, 3+t, 3-t, 3+2t, 3-2t`. Its allowed full lattice
is precisely `gcd(a²+2b²,1122)=1`, with **204,800** permitted
residues modulo 1122, decomposing into **6,688** finite components
of maximum size **2,283**. This last number is the exact maximum
in the full *allowed sieve*, not the exact irreducible-prime graph
maximum.

For the graph on irreducible elements themselves we additionally
prove an **exact 90-vertex connected component** containing every
irreducible dividing 1122 up to associates. Its finite overgraph
closure has 92 points, the only nonirreducibles being the units
`+1,-1`. Every other prime component has at most 2,283 points,
so the rigorous uniform range is

\[
    \boxed{90\ \le\ \max |\text{irreducible component}|\ \le\ 2283}
       \qquad(\sqrt6\le D<\sqrt8).
\]

The previous [radius-two theorem](../sqrt-minus-two-radius-two/README.md)
gave the optimal principal-sieve period **6** throughout
`2 <= D < sqrt(6)`. The new four norm-six directions cause a
**sharp factor-187 period jump** at `D=sqrt(6)`.

## Proof evidence and independent replay

All data required to recheck the infinite results is public:

- `lower_cycles.json.gz`: 682 literal nonzero-period admissible
  walks, one for **every** squarefree scalar `1 <= q < 1122`,
  each at most 561 moves. Lemmas 2.2 and 3.1–3.2 turn these into
  obstructions for **all** smaller periods, including nonsquarefree
  periods and composite-generator lists.
- `positive_q1122.json.gz`: every integer point in each of 6,688
  connected finite pieces. The checker independently checks all
  **1,258,884** residue pairs for coverage, literal allowed
  neighbor closure and connectedness. Lemma 4.1 proves that
  these finite checks imply the complete infinite decomposition.
- `exceptional_closure.json`: the 92-point closed exceptional
  overgraph, with exact exhaustive integer-factor primality
  tests and connectivity of all 90 irreducibles.

Run from this note's directory:

```sh
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The checker uses **only Python standard-library integer arithmetic**
(no solver or floating-point inequality), never imports producer
code, and raises explicit exceptions even with optimized Python.
The negative mutation suite confirms altered paths, incomplete
positive partitions, and invalid exceptional sets are rejected.
Exact original witness bytes are included, not just a hash or a
stored success flag.

The **nontrusted producers** are
`code/generate_negative.cpp`, `code/generate_positive.cpp` (C++17)
and `code/generate_exceptional.py`. The C++ producers rebuild the
lower-period JSON array on standard output and the positive JSON
partition on standard output; gzip compression of those streams
reconstructs the corresponding proof data. They are not invoked
by the checker, and their successful output is not used as a
mathematical axiom. Full reproduction and trust boundaries are
specified in [AUDIT.md](AUDIT.md).

## Research provenance and limitations

This is additive to our earlier
[small-radius](../sqrt-minus-two-sharp-moats/README.md) and
[radius-two](../sqrt-minus-two-radius-two/README.md) work.
The finite principal-ideal strategy follows the OpenAI/math
Gaussian-prime result (family 028, pinned public commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`), as adapted
in entry 002's all-quadratic-order programme. The new specific
number-theoretic theorem, finite witnesses, proof and checker
are separately attributed; historical sources are preserved.

**Open:** The actual maximum irreducible-component size at this
step threshold remains between 90 and 2,283. Neither an exact
maximum nor a classification of all optimal-period generator lists
is asserted here. External human review, complete literature
matching and Lean formalization are outstanding. We make no
novelty or first-discovery claim.
