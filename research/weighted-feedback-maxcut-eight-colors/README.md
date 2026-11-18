# Weighted MaxCut versus random-cut imbalance for eight-colorable graphs

The BEKSZ inequality holds for arbitrary nonnegative edge weights whenever the graph formed by the strictly positive edges admits a proper coloring with at most eight colors. There is no bound on its number of vertices. A counterexample to the general conjecture, if one exists, therefore needs at least nine colors.

The [proof](PROOF.md) contracts independent color classes, then shows that a smallest counterexample is witnessed by a facet of a complete-graph cut polytope whose outward normal is positive in every edge coordinate. The normalized objective is checked for every relevant orbit at orders up to eight. Completeness of the underlying enumeration is a published theorem, not a consequence of the checking programs.

This is neither an equality classification nor an unrestricted weighted result. It does not settle the 7/23 feedback-channel threshold. The [unweighted result](https://github.com/mxym/math/pull/110) covers all chromatic numbers but is restricted to equal present-edge weights. See [sources](SOURCES.md) and the [independent internal review](REVIEW.md). This AI-assisted draft is not externally peer reviewed and bibliographic priority is unconfirmed.

## Reproduction (Python standard library)

The catalog is not bundled or republished. With internet access, run:

```sh
python3 -B -O verify.py --download
python3 -B -O independent.py --download
```

Alternatively, save the four official raw files linked in [SOURCES.md](SOURCES.md), named `swcut_5` through `swcut_8`, to one directory and pass `--source-dir DIRECTORY` in place of `--download`. The parser requires the exact indexed coefficient rows and fails on any digest mismatch, missing row, reordered edge, malformed inequality or unrecognized file format. Both computation paths use the same pinned input. [CHECKS.txt](CHECKS.txt) records the exact outputs; the actual objective computations are independent.
