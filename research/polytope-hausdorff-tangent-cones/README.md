# Hausdorff limits for random approximation of a polytope

Sample $n$ independent uniform points in a fixed full-dimensional polytope $K$ or on its boundary, and take their convex hull. In all dimensions, the normalized Hausdorff error has a limiting distribution with **one independent factor per vertex**. This answers the higher-dimensional polytopal question in [Sonnleitner's introduction](https://arxiv.org/html/2508.16442v1#S1), immediately before Remark 2.

The normalization is $n^{1/d}$ for volume sampling and $n^{1/(d-1)}$ for surface sampling. At each vertex, take a Poisson process on the tangent cone (or its surface) of intensity equal to the reciprocal of the original volume (or surface area). The limiting error is the maximum of the distances from the respective cone apices to these independent Poisson hulls. No combinatorial simplicity assumption is required. The entire vector of vertex errors converges in total variation, and every positive moment of the normalized Hausdorff error converges.

[The analytic proof](PROOF.md) shows why distant sample points cannot affect the limiting distance, including at obtuse corners. It gives a finite sum of deterministic integrals for each vertex factor. As a check of the geometric interpretation, in the surface model at a planar right angle the first point on each incident ray has independent exponential distance $X,Y$ of rate $1/\mathcal H^1(\partial K)$. The perpendicular foot lies on the segment joining them, so the factor is the law of $XY/\sqrt{X^2+Y^2}$. The polygon result is prior work, not the novelty.

[SOURCES.md](SOURCES.md) distinguishes the earlier planar distributions, higher-dimensional rate bounds and simple-polytope local scaling results. This is not a theorem about varying polytopes, a Gumbel law, or the question of nonoptimal sampling density on a smooth body.

AI-assisted working research; [independent internal AI audit](REVIEW.md), not external peer review or proof-assistant certification. No priority claim.
