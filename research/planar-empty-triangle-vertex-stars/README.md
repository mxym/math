# A linear upper bound for the largest planar vertex star of empty triangles

Among \(n\) independent points drawn uniformly in a fixed planar convex body, choose the vertex incident to the most empty triangles. The expected number of incident triangles is **of order \(n\)**. This concerns a common *vertex*, not a common edge.

The rate itself was already stated by Reitzner and Temesvari in their 2018 preprint. Their 2019 revision gives an \(O(n\sqrt{\log n})\) planar upper bound and asks whether the logarithm can be removed; their 2023 slides repeat the latter bound. The lower bound is known. This note proves a linear upper bound by controlling the fourth centered moment for a fixed anchor, uniformly over its location. It counts both triangles created and triangles destroyed by an insertion; the difference need not be positive. See the [source/version comparison](SOURCES.md).

- [Analytic proof](PROOF.md) and [independent internal review](REVIEW.md).
- Optional `python3 -B -O check.py`: exact checks of the insertion/deletion bookkeeping on finite integer configurations, not a verification of the asymptotic theorem.
- [Separate intermediate-dimensional star result](../intermediate-empty-simplex-stars/). That result excludes both endpoints; it does not imply this planar bound. No leading constant or distributional limit for the planar vertex star is asserted here.

AI-assisted research draft, internally audited and not externally peer-reviewed. No claim of publication priority.
