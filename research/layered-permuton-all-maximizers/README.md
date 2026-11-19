# Layered patterns have only layered optimal permutons

Kabela, Král’, Noel and Pierron asked whether a layered permutation can have a nonlayered density-maximizing permuton ([Problem 3](https://doi.org/10.37236/10781)). **For every pattern with at least two points, the answer is no.** Even with singleton layers, including adjacent ones, all maximizing permutons avoid 231 and 312. Equivalently, every limit point of an unrestricted near-optimal sequence is layered. The pattern of order one has constant density and is the trivial exception.

The [proof](PROOF.md) uses two incomparable copies of a point to compare labelled completions of the target. On an interval spanned by inversions, those tests force every successful internal segment to be monotone. If that interval supports both increasing and decreasing pairs, replacing it first with either pure orientation and then with a uniform permuton gives a contradiction.

This is a limit theorem. It does not say all finite optimizers are layered, that the number of layers is bounded, that all optimal layer masses are known, or that a given pattern has a unique optimal permuton. It generalizes the layeredness step of the [single-pattern 1324 note](../packing-density-1324-unrestricted/), not its uniqueness conclusion.

## Verification

The proof is analytic, independent of computation. [check.py](check.py) illustrates the clone comparisons on every layered target through order eight, the inversion components on every permutation through order eight, and the substitution identity on 240 rational block laws/sample-order pairs. Reproduce the expected output using Python 3.10+ with no dependencies:

```sh
sha256sum -c SHA256SUMS
python3 -B -O check.py | diff -u CHECKS.txt -
```

See [SOURCES.md](SOURCES.md) for the prior results and bounded search, and [REVIEW.md](REVIEW.md) for the separate internal check of the frozen proof. AI assisted the derivation, drafting, and internal review. This is not external peer review; no priority or publication claim is made. Third-party papers retain their own rights.
