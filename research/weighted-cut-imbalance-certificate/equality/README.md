# Equality in the weighted BEKSZ cut–imbalance inequality

In a finite loopless undirected graph with nonnegative edge weights of positive total, **equality is possible only for a uniformly weighted triangle or a uniformly weighted five-clique**, and both attain equality. Arbitrarily many isolated vertices may be adjoined. Parallel edge weights are first added, and edges of weight zero do not count. The all-zero graph is a separate, trivial equality.

Braverman, Efremenko, Kol, Saxena and Zhang [already gave these two examples](https://doi.org/10.4230/LIPIcs.ITCS.2025.22). This addendum classifies *all* extremizers even when edge weights are arbitrary real numbers. It builds on [the weighted inequality and its exact certificate](../README.md). It does not give a new coding threshold, characterize optimal codes or assert a quantitative stability bound.

## How the proof works

The old certificate bounds the absolute first moment of a random signed degree sum by interpolation on closed polygons. Two exact replays identify **three** tight parameter/vector pairs. One is not the degree vector of any extremal graph. To pass from this relaxed calculation to the actual graphs, equality must give the same maximizing sign function at every contributing corner. A majority of three signs cannot agree with a majority of five on every outcome. This forces all the graph's degree weight onto three or five vertices. In the five-vertex case all ten two-versus-three cuts must have the same weight, which uniquely fixes every edge.

## Reproduction

From **this directory**, using Python 3 with its standard library:

```sh
sha256sum -c SHA256SUMS
python3 -B -O verify_equality.py ..
python3 -B -O independent_equality.py ../certificate.json
```

The first checker verifies the exact hashes of the [original certificate](../certificate.json) and [original verifier](../verify.py). The second takes only the certificate and independently computes the relevant inequalities, convex polygons, extremal vectors and sign expectations. Both check failures explicitly, so Python's optimization flag does not disable verification. Compare their outputs with [the first run](AUTHOR-CHECKS.txt) and [independent run](INDEPENDENT-CHECKS.txt). As a supplementary test, the latter also enumerates all 59,048 nonzero five-vertex graphs with individual edge weights in {0,1,2}; the theorem for arbitrary real weights does **not** follow from this sample.

[Proof](PROOF.md) · [Independent internal review](REVIEW.md) · [Prior work and search limits](SOURCES.md)

AI-assisted mathematics and independent internal AI review; not externally peer reviewed or formally verified in a proof assistant. No priority claim.
