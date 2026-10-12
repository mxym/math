# Layered norm refinement: global prime-component bound 241

Research note, 8 October 2026. [Complete proof](paper.md) ·
[independent exact checker](code/check_exact.py) ·
[replay log](results/replay.txt) · [proof audit](AUDIT.md).

## Result

For the graph on **all irreducible elements** of
`Z[sqrt(-2)]`, with genuine complex Euclidean step radius
`sqrt(6) <= D < sqrt(8)`, we establish

\[
               \boxed{90\le B_D\le241}.
\]

The lower endpoint comes from the previously proved exactly
**90-vertex closed prime component**; every other prime component
has at most **241** vertices. This substantially improves the
predecessor bound `90 <= B_D <= 2283`. **We do not assert that
241 is the actual prime-graph maximum.**

More precisely, the **refined lattice sieve**

```text
gcd(a*a + 2*b*b, 1122 * 19 * 5) == 1
```

has exact largest connected component size **241**. That number
is attained by an explicit translate of a previously certified
finite quotient component. The proof does **not** enumerate all
residues modulo 106,590; instead, it proves a general **iterated
finite-component congruence refinement lemma**. This permits
pruning small components of any existing periodic partition.

## Exact verification

The proof reuses two immutable files from the
[sharp period-1122 theorem](../sqrt-minus-two-sqrt6-period/README.md):
its complete 204,800-vertex quotient partition and 92-point
exceptional closure. Their exact byte SHA256 digests are pinned
by `code/check_exact.py`; no new gigantic witness data are
needed. The checker independently computes:

| Exact finite test | Replayed result |
| --- | ---: |
| Original parent components larger than 241 | 190 |
| First-stage mod-19 shifts checked | 68,590 |
| First-stage components larger than 241 | 8 |
| Maximum first-stage component | 298 |
| Second-stage mod-5 shifts checked | 200 |
| Maximum refined component | **241** |

It verifies that the six additional exceptional irreducibles
above rational primes 5 and 19 all already belong to the
**same old 90-prime component**. No new exceptional component
is overlooked.

From this directory run:

```sh
(cd ../sqrt-minus-two-sqrt6-period && python3 code/check_exact.py)
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The verifier is standard-library Python with **exact integers
only**. It computes all required finite quotient-component
adjacencies, enforces the bound on every congruence shift, and
uses explicit exceptions rather than disabled `assert` checks.
The mutation suite rejects changed upstream hashes, missing
special primes, duplicate lattice representatives and graph
traversal defects.

## Attribution and boundaries

This is a continuation of repository entry 002 and the
independently certified [period-1122 theorem](../sqrt-minus-two-sqrt6-period/README.md).
The general periodic ideal-sieve method traces to OpenAI/math
family 028, pinned at
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The present note supplies the extra hierarchical refinement lemma,
its independent arithmetic verification, and the stronger bound.

There is no external human peer-review, worldwide novelty
assessment, or full Lean formalization claim. The exact maximum
prime-only component size remains open within the displayed
interval. The old parent theorem and certificate bytes are
not modified.
