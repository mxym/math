# How many empty convex polytopes does a random point set span?

Choose \(n\) independent uniform points from a fixed convex body \(K\) in \(d\)-dimensional space. A \(k\)-hole is a choice of \(k\) points that are all vertices of their convex hull, with none of the other sampled points inside. Two questions of [Balko, Scheucher and Valtr](https://arxiv.org/pdf/2111.12533) concern the coefficient of the leading \(n^d\) term of the expected count.

1. **Existence for every fixed dimension and size.** [Proof and integral for the coefficient](PROOF.md). For every fixed \(d\ge2\), \(k\ge d+1\) and full-dimensional convex body, the expected count divided by \(n^d\) converges to a finite positive limit. The order of growth and positivity were known. What the argument adds is convergence for all the remaining cases \(d\ge3,\ k\ge d+2\). It does not assert the same constant for all bodies.
2. **The value for tetrahedra in a tetrahedron.** [Exact evaluation](TETRAHEDRON.md). For \(d=3,k=4\), with a tetrahedron as the sampling body, the coefficient is \(9/4+3\pi^2/35\), about 3.095966. Here existence and the section-integral formula were already known; the calculation supplies the exact number requested in Problem 1, consistent with the authors' simulation.

[Sources and scope](SOURCES.md) distinguish the earlier area and counting results, revisions, and dated overlap checks. [Review of existence](REVIEW.md) and [review of the evaluation](TETRA-REVIEW.md) are independent internal mathematical checks, not external peer review. No priority guarantee is implied.

The proofs are analytic. To replay the finite rational arithmetic in the second proof, run `python3 -B -O exact.py` and compare [CHECKS.txt](CHECKS.txt). No nonstandard library or simulation is needed.
