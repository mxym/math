# The weighted degree-square Max-Cut conjecture with at most three exceptional vertices

Let $W>0$ be the total weight of a finite loopless undirected graph with nonnegative edge weights, let $C$ be its maximum cut weight, and let $d_i$ be its weighted degrees. We prove
$$ C\ \ge\ \frac{W}{2} + \frac{1}{8W}\sum_i d_i^2 $$
in two settings:

1. **All but at most three vertices have the same weighted degree.** The three exceptional degrees need not agree, the order of the graph is unbounded, and no symmetry is required of the individual input edge weights.
2. **Product weights:** $w_{ij}=x_i x_j$ for nonnegative vertex parameters. Here there is no restriction on the number of different degrees.

These are partial results for [Braverman, Efremenko, Kol, Saxena and Zhang, ITCS 2025, Conjecture 5](https://doi.org/10.4230/LIPIcs.ITCS.2025.22), numbered 1.5 in their [ECCC full version](https://eccc.weizmann.ac.il/report/2022/179/revision/1/download/). They gave the equal-weight odd cliques as sharp examples. The degree-square lower bound is **not** the different one-feedback cut–imbalance inequality of [#123](https://github.com/mxym/math/pull/123); this result does not give any new communication threshold. It is not a proof for unrestricted weights, and it does not classify all equality cases.

## Proof guide

- [Product weights](RANK-ONE.md): a greedy choice of signs bounds the partition discrepancy; a variance identity completes the proof.
- [Two exceptional vertices](TWO-EXCEPTIONS.md): averaging over the equal-degree vertices preserves every degree and cannot increase the maximum cut. At a strictly positive vertex of the resulting four-parameter polytope, all four active cut types force product weights.
- [Three exceptional vertices](THREE-EXCEPTIONS.md): seven parameters and four exceptional sign patterns leave just one additional family to check, arising when a signed count reaches the end of its allowed interval. The degree-square gap has an exact positive polynomial expansion throughout that family. The [independent review](REVIEW.md) gives a second, symmetric identity using an explicit cut.

## Reproduce the checks

From this directory, using Python 3 and the standard library:

```sh
sha256sum -c SHA256SUMS
python3 -B -O three_check.py
python3 -B -O independent.py
```

[First output](AUTHOR-CHECKS.txt) · [Independent output](INDEPENDENT-CHECKS.txt) · [Sources and scope](SOURCES.md).

The first script reconstructs the polynomial by formal integer arithmetic. The independent one verifies a separate symmetric identity by exact interpolation on a determining grid and separately recovers the sorted positive-coefficient expansion. Bounded graph enumerations are additional checks, not evidence substituting for the proof at unbounded orders. The zero-total case can be read in the division-free form $8WC\ge4W^2+\sum d_i^2$. Parallel edge weights are aggregated.

AI-assisted manuscript and independent internal AI review; no external peer review, proof-assistant formalization or assurance of priority.
