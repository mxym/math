# Sharp radius-two transition and complete period-six sieve rigidity

Research continuation, 8 October 2026. [Complete written proof](paper.md) ·
[static integer proof certificates](code/certificate.json) ·
[independent exact checker](code/check_exact.py) ·
[replay transcript](results/replay.txt) · [scope audit](AUDIT.md).

## Main results

Let `t = sqrt(-2)`, and let `G_D` join all irreducible **elements** of
`Z[t]` whose genuine complex Euclidean distance is at most `D`. This
note continues our [earlier complete small-radius theorem](../sqrt-minus-two-sharp-moats/README.md)
beyond the previously untreated radius two.

For **every real** `2 <= D < sqrt(6)`, the prime graph consists of
exactly two exceptional **7-vertex components** and only isolated
vertices or 2-vertex edges otherwise. The two large components are

- `{t, 1+t, -1+t, 3+t, -3+t, 3+2t, -3+2t}`;
- its complex conjugate.

The complete classification of the remaining edges is given by two
explicit infinite families of paired coefficient points in Theorem A.
Together with the previous `D<2` theorem, the exact maximum-size
phase diagram is:

| Euclidean radius | Exact largest connected component |
| --- | ---: |
| `0 <= D < 1` | 1 |
| `1 <= D < 2` | 3 |
| `2 <= D < sqrt(6)` | **7** |

The new jump occurs **exactly** at `D=2`. No larger value at smaller
radius is inferred from mere finite computation: the proof gives a
complete analytic decomposition of the periodic complement plus an
independently certified finite exceptional closure.

For the ten geometric steps of norm-squared at most four, the
**smallest** successful finite principal-ideal sieve scalar period
is **6**. At this period, *every successful generator list*,
including arbitrary composite generators, **must contain all three**
principal ideals `(t)`, `(1+t)` and `(1-t)`. Conversely their joint
presence is sufficient. Thus the minimum number of generators rises
from two for the previous eight-neighbor step set to **three** for
the ten-step set; the smallest list is unique up to associates and
order. The actual infinite allowed lattice decomposes into pairs.

## Exact replay

From this directory:

```sh
python3 code/check_exact.py
python3 -O code/check_exact.py
python3 code/self_test.py
python3 -O code/self_test.py
sha256sum -c SHA256SUMS
```

The independent checker verifies eight representatives forming four
closed two-point quotient components, a 16-point exceptional closure
with exactly two prime clusters of size seven, three negative
period-six walks of lengths 4,12,12, and five lower-period walks.
It also executes a separate full test of **all 2,048 subsets** of the
11 scalar-six divisor ideals; exactly **256** are successful, precisely
those containing the required three prime ideals. Negative mutation
tests confirm that incorrect data are rejected even with optimized
Python assertions disabled. Only standard-library integer arithmetic
is used; no solver, floating-point inequalities or network is needed.

`code/produce.py` is a nontrusted witness producer and is **never
imported** by the checker. The mathematical bridge from finite tests
to infinite conclusions is proved explicitly in the [paper](paper.md)
through periodic-lift, nonzero-voltage and exhaustive ideal-domination
lemmas. The exact witness data, rather than a stored success Boolean,
are included.

## Provenance and scope

This is an additive continuation of the earlier independent
`Z[sqrt(-2)]` result and manuscript 002's quadratic-order programme.
Its finite-sieve method is based in part on
[OpenAI/math](https://github.com/openai/math) family 028, pinned
at `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, with upstream
attribution and original methods distinguished in the manuscript.

The statements hold only for the specified ring and step ranges;
`D >= sqrt(6)` is not settled. All mathematical conclusions are
written and supported by replayable integer witnesses, but **not
Lean-formalized or externally refereed**. No worldwide novelty or
first-priority claim is made. Historical source snapshots remain
unchanged.
