# The largest empty simplex whose vertices are data points

Sample independent uniform points in a fixed convex body in dimension d ≥ 2. Almost surely the largest empty simplex with sample vertices has volume asymptotic to d times the body's volume times (log n)/n. The same holds for the largest empty polytope with sample vertices. In particular, in the plane an empty triangle already achieves coefficient 2, not the coefficient 1 conjectured for polygonal holes by Arizmendi–Salazar in connection with their Theorem 1.3.

The unrestricted leading constant was proved by **Peres and Yang** in October 2026; we use their result for the upper bound. The point here is the matching lower bound with all vertices required to be among the data and with the minimum possible number of vertices. We do not claim their unrestricted result, a new thin-target principle, or a theorem about lacunary dilates.

[Proof](PROOF.md) · [Sources and comparison](SOURCES.md) · [Independent internal review](REVIEW.md)

The proof is analytic. The optional standard-library replay, `python3 -B -O check.py`, checks finite instances of the minimum-volume corner selection and a block-occupancy identity; it is not a proof of the asymptotic estimate. Expected output is in [CHECKS.txt](CHECKS.txt); the file digests are in [SHA256SUMS](SHA256SUMS).

AI-assisted research with a separate AI-assisted internal proof review. Not externally peer reviewed; the comparison is bounded and no priority guarantee is made.
