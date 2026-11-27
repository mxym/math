# Exact eventual Walsh-support cardinalities for ternary functions

For scalar \(f:\mathbb F_3^n\to\mathbb F_3\), a positive integer is the number of nonzero Walsh coefficients in some finite dimension if and only if it is **not** one of **2, 4, 5, 8, 10, 11**. The result also determines the exact attainable sets for \(n=1,2,3\). It does not assert the minimum dimension of realization for every larger size.

The [proof](PROOF.md) combines a phase-specific midpoint rule, an affine-dimension bound, two exact small-dimensional exclusions, and a ternary-function join that constructs every size at least 12. It addresses the ternary eventual-attainability part of the [p-ary question in Jauberty–Méaux §8](https://opencryptology.org/2025/1651/versions/20260428T172000Z.pdf), not its unrestricted prime or fixed-dimension forms. The [source notes](SOURCES.md) state the distinction and prior-art limits.

## Reproduce

Requirements: Python 3.10 or later and a GCC- or Clang-compatible C++20 compiler on a 64-bit platform providing an unsigned 128-bit type. No downloads or nonstandard libraries are needed.

    bash replay.sh

This compiles into an automatically removed temporary directory. [RESULTS.txt](RESULTS.txt) records the output. For the truth-table witnesses and construction alone:

    python3 -B verify.py
    python3 -B verify.py --construct 58

The constructor prints a ternary truth table in least-significant-coordinate-first order, together with its dimension and its recursive construction steps. It is not optimized to give the lowest possible input dimension.
