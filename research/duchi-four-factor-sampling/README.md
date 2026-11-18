# Duchi’s matrix sampling inequality: four factors suffice for failure

For each population size $n\ge5$, there exist $n$ rational real symmetric positive-semidefinite contractions such that the expected **operator norm of an ordered four-factor product** is greater for sampling without replacement than with replacement. Each individual norm is taken *before* averaging. The construction for five matrices has dimension 120; its positive gap is exactly $143122330764557928036854/140853128766496215082650125$.

**Why four matters.** Israel, Krahmer and Ward gave the positive result through three factors. De Sa had already disproved the general inequality at six, and Liu gave a separate six-factor family and exact counting formula. This note uses their symmetrization approach but a different weighted planar template to reach four, the smallest length for which failure is possible. It does **not** decide the case of four matrices sampled four at a time, find the optimal dimension, or determine the optimal ratio.

[Theorem, construction and exact pattern table](PROOF.md) · [Independent internal audit](REVIEW.md) · [Prior-art search scope](SEARCH.md)

To reproduce the arithmetic with only the Python 3.8+ standard library, run from this directory:

```sh
python3 -B -O verify.py
python3 -B -O check.py
```

The first verifier uses rational overlap products. The independent second verifier multiplies scaled integer matrices and checks the polynomial coefficients as well as every ordered word over four, five and six labels. Both use explicit exceptions even in optimized mode.

**Status:** AI-assisted research draft; internally reviewed by AI, not externally peer reviewed or formally verified in a proof assistant. No guarantee of historical priority.
