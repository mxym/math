# Six points in convex position: the ellipse maximum

Let six points be sampled independently and uniformly by area in a planar compact convex body of positive area. The probability that all six are vertices of their convex hull is at most

$$1-\frac{305}{24\pi^2}+\frac{473473}{11520\pi^4}\;\approx\;0.1343093864,$$

with equality exactly for ellipses. [Marckert](https://doi.org/10.1214/16-BJPS315) evaluated the probability in a disk; the result here is the sharp comparison with **every** such body, proved by showing that Steiner symmetrization cannot decrease the probability. Together with the separate [triangle minimum, 91/900, attained only by triangles](https://github.com/mxym/math/pull/194), this answers the six-point specialization of [Marckert–Rahmani's Conjecture 1](https://doi.org/10.1112/mtk.12110). Neither result settles the conjecture for larger sample sizes.

The [proof](UPPER.md) fixes the six horizontal coordinates and uses the authors' two-comb recurrence to compare the conditional probabilities before and after centering each vertical chord. The conditioned gap is a quartic polynomial in the chord data. A reduction to the signs of four slope differences and an exact positivity certificate prove the comparison. Strictness and affine normalization identify the maximizers.

**Replay.** With Python 3.9+, NumPy, a C++17 compiler named `g++`, and GMP development files on a platform with 64-bit `unsigned long`, run from this directory:

```sh
sha256sum -c SHA256SUMS
OPENBLAS_NUM_THREADS=1 python3 -B -O upper_exact.py > replay.txt && cmp replay.txt CHECKS.txt
```

[Python driver](upper_exact.py) · [exact C++/GMP determinant verifier](upper_pack.cpp) · [unchanged polynomial evaluator from #194](lower_exact.py) · [expected full output](CHECKS.txt). No downloaded table, discovery cache or network access is required. The driver reconstructs 715 coefficient polynomials on an exact unisolvent grid. The verifier certifies all 292 required determinant coefficient polynomials, with 8,798,236 positive monomials counted across them. An independent internal reviewer read the mathematics and code and reran the frozen sources from scratch; the full output matched byte for byte. This was a replay of the **same implementation**, not a second independently written verifier.

[Independent internal review](REVIEW.md) · [primary sources and search scope](SOURCES.md). AI-assisted, exact computer-assisted proof; not externally peer reviewed or verified in a proof assistant. No claim of priority.
