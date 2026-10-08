# Sharp small-radius prime graphs and optimal periodic sieves in Z[sqrt(-2)]

Research note, 8 October 2026.

**[Complete theorem statements and written proof](paper.md)** ·
[exact witness data](code/certificate.json) ·
[independent integer checker](code/check_exact.py) ·
[replay log](results/replay.txt) ·
[proof and novelty-scope audit](AUDIT.md)

## Main results

Write `t=sqrt(-2)` and draw the graph on **all irreducible elements**
(not associate classes), with Euclidean edge length at most `D`.
For *every real* `0 <= D < 2`, the graph is completely classified:

| Radius | Two exceptional components | All remaining components | Sharp global size |
| --- | --- | --- | ---: |
| `0 <= D < 1` | No edges | Isolated vertices | 1 |
| `1 <= D < sqrt(2)` | Exactly two 3-vertex paths, centered at `+t,-t` | Isolated vertices | 3 |
| `sqrt(2) <= D < 2` | The same two 3-vertex paths | Isolated vertices or single vertical edges | 3 |

The graph **does not change** upon crossing the geometric step
threshold `sqrt(3)`. An ordinary 2-vertex component is given by
`3+t` and `3+2t`, whose norms are rational primes 11 and 17.
Theorem A supplies an exact criterion for every other possible
2-vertex component. The theorem is an infinite-graph statement,
not an assertion based on a coordinate cutoff.

For the eight coefficient-neighbor steps (precisely the Euclidean
steps of squared norm at most three), the smallest successful
finite principal-ideal sieve scalar period is **6**. At this optimal
period, *all* successful generator lists, including arbitrary
composite generators, are characterized: the list must contain the
ideals in at least one of

- `{(t),(1+t)}`;
- `{(t),(1-t)}`;
- `{(2),(1+t),(1-t)}`.

These are precisely the **three inclusion-minimal successful lists**.
The two-generator minimum is sharp and its two minimizers are completely
classified. The third list gives a distinct minimal three-generator
solution, not simply a redundant enlargement of a two-generator one.

## Reproduction

Run in this note's directory:

```sh
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The independent checker uses only Python standard-library exact
integer arithmetic. It checks all **12** static finite witnesses:
three positive quotient partitions, four nonzero-translation walks
for maximal failing ideal families, and five lower-period paths.
In addition, its separate exhaustive 36-state quotient test checks
**all 2,048 subsets of the 11 divisor ideals**, finding exactly
896 successful lists, precisely those covered by the three-base
theorem. Mutation tests verify that incomplete partitions,
mis-stated ideals and invalid paths are rejected even under `-O`.

`code/produce.py` is the deterministic **untrusted producer**, and
`code/check_exact.py` never imports it. The infinite mathematical
conclusions rely on the lifting lemmas and algebraic argument in
`paper.md`; a generator returning `True` is not itself a proof.

## Provenance and limitations

This continues [manuscript 002](../../preprints/002-quadratic-order-moats/README.md),
which develops finite principal-ideal sieves for quadratic orders,
inspired by the [OpenAI/math Gaussian-prime work](https://github.com/openai/math)
(family 028, pinned snapshot
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`). It studies a
different imaginary quadratic ring and supplies its own proofs,
classification, exact witnesses, and separate checker.

The work was prepared with AI assistance. It is a complete
**written research proof with exact computational certificates**,
not a Lean proof, external peer review, a full literature survey,
or a claim of world-first discovery. Radius 2 and larger remain
outside this note. Existing original and parallel manuscripts are
not modified or overwritten.
