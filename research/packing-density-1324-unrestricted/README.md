# Unrestricted uniqueness for packing 1324

Exactly one permuton attains the maximum limiting density of the classical permutation pattern 1324. It is the symmetric, infinitely layered permuton characterized in [the companion proof](../packing-density-1324/PROOF.md). Consequently *every* sequence of permutations with orders tending to infinity and density tending to the maximum has that same limit. No hypothesis of layering is needed on the sequence or the maximizing permuton.

The companion note proved uniqueness **within** the layered class. Existence of a layered optimum would not by itself exclude another, nonlayered optimizer. [The present proof](ALL.md) tests an arbitrary extremal measure by replacing a small amount of mass with incomparable copies of one point. The resulting second-order inequality forces the two forbidden three-point pattern densities to vanish. There is also a short finite counterpart: at order at least four every exact maximizer is layered, but its finite layer sizes and uniqueness are not determined.

This is a statement about maximizing occurrences, **not** the 1324 avoidance problem. It introduces no new numerical record or quantitative rate of convergence. See [sources and scope](SOURCES.md) and the [independent internal mathematical review](REVIEW.md). The development and review were AI-assisted and do not constitute external peer review.

An optional Python 3 standard-library checker enumerates small permutations and replays both the finite clone identity and second-order coefficients in weighted examples. These are sanity checks, not a substitute for the proof for all permutons:

```sh
sha256sum -c SHA256SUMS
python3 -B -O check.py | diff -u CHECKS.txt -
```
