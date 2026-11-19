# Minimum pairwise overlap of crossing geodesic tubes in higher dimension

Take distinct complete geodesics that intersect pairwise inside real hyperbolic space of curvature −1 and dimension $D\ge3$. Thicken each to a tube of radius $\delta>0$. For every $s>0$, sum the $s$th powers of their pairwise intersection volumes, counting ordered pairs.

- A nonconcurrent arrangement can always be strictly improved by moving the geodesics through one point.
- When the number $N$ of geodesics is at most $D$, the minimizers are exactly the concurrent orthogonal directions.
- When $N>D$ **and a real equiangular tight frame of $(N,D)$ exists**, the minimizers are exactly the concurrent realizations of those frames. In particular, for $N=D+1$ the regular simplex directions are the unique optimum up to isometry and labels, for every width and positive exponent.

There is no exact optimizer classification here for parameters admitting no real equiangular tight frame. Disjoint or asymptotically meeting geodesics are not allowed. This is a higher-dimensional companion to the [hyperbolic plane theorem](../hyperbolic-crossing-tube-overlap/README.md), not an exact higher-dimensional conjecture stated by Steinerberger.

[Proof and minimum values](PROOF.md) · [Independent internal review and an alternative kernel identity](REVIEW.md) · [Primary sources and search limits](SOURCES.md). The bridge to classical frame optimization is the strict log convexity of the geometric intersection volume as a function of the **squared** directional inner product, which works even for $s<1$.

This is AI-assisted mathematical work (including Dreamer-assisted exploration) with independent AI internal review. It is not externally peer reviewed and no priority is claimed.

## Checks

Run `sha256sum -c SHA256SUMS`, `python3 -B -O check.py` and `python3 -B -O independent.py` in this directory. The two exact standard-library checks cover metric normalization, the one-pair integral's branch and the equality examples. Expected outputs: [author](CHECKS.txt), [independent](INDEPENDENT-CHECKS.txt). The analytic argument, not those finite checks, proves the claims.
