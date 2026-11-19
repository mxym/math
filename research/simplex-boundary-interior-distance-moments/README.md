# Boundary versus interior distances on simplices: the dimension threshold

Choose two independent points uniformly by surface area on a nondegenerate Euclidean simplex, and another pair independently by volume. In which dimensions is the surface pair at least as far apart in **every real moment of order $p\ge1$, for every simplex**?

- **Dimensions 1, 2 and 3: yes.** In fact, for every linear projection and every threshold $t\ge0$, its expected positive excess over $t$ is at least as large for the signed surface-pair difference as for the signed volume-pair difference. Symmetry makes this a one-dimensional convex-order comparison. Averaging projected absolute moments gives the Euclidean result. The proof allows any facet probabilities bounded by $1/2$, with uniform sampling on the chosen facet.
- **Every dimension $d\ge4$: no.** For each fixed $1\le p<d(d-3)$ a family of nondegenerate simplices gives the *strict reverse* Euclidean inequality. Two colliding vertices produce limiting longitudinal laws with an explicit beta-moment ratio. Nothing here decides what happens at or above the displayed range in a fixed higher dimension.

[SIMPLEX.md](SIMPLEX.md) gives both proofs. The positive proof in dimensions 2 and 3 is computer-assisted: after the analytic reduction, [verify.py](verify.py) covers every polyhedral sign region and reconstructs its exact integer polynomial. To reproduce [CHECKS.txt](CHECKS.txt) using only Python's standard library:

    python3 -B -O verify.py

There are 4 simplicial cones in the triangle certificate and 15 in the tetrahedron certificate. No numerical approximation or sampling enters the sign proof. [REVIEW.md](REVIEW.md) records an independent internal proof and code audit. The negative construction is analytic.

This is a classification **for simplices** in the all-powers question associated with Zaporozhets and Tarasov. It does not solve the all-powers problem for arbitrary nonsymmetric planar convex bodies. Neither multivariate convex order nor ordinary stochastic dominance of the distances is asserted. The planar first and second moments and higher-dimensional counterexamples among unrestricted convex bodies are prior results: see [SOURCES.md](SOURCES.md).

AI-assisted working research. Internal AI review, not external peer review or formal proof-assistant verification; no priority guarantee.
