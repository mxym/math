# A random fragmentation-area limit for discrete subtree powers

**Yongxian Zhang.** For every internal clade in the critical beta-splitting tree, raise its leaf count to a fixed real power p and add the results. Below p=1 the sum divided by n approaches a constant. At p=1 the normalization is n(log n)². Above p=1, even the leading answer varies from tree to tree: dividing by nᵖ log n gives a **nonconstant** limit in every finite Lᵠ under the standard fragmentation coupling. The limit is a previously studied self-similar fragmentation area, now obtained from the sampled discrete tree. At p=2 it has mean 1 and variance 2/11.

[The critical-window supplement](WINDOW.md) gives the deterministic interpolation for p=1+λ/log n, uniformly over bounded λ-intervals. The problem is [Aldous–Janson II, Open Problem 16](https://arxiv.org/html/2303.02529v3#S6.SS2). This note treats fixed **real** powers and that window, not complex powers or second-order limits.

[Proof](PROOF.md) · [Prior work and precise scope](SOURCES.md) · [Independent internal review](REVIEW.md). The integer-power means were already implicit in Fuchs–Steel, the critical mean/variance and subcritical mean were prior, and Bertoin established the continuum area law and moment recursions. AI-assisted research; not externally peer reviewed; no priority guarantee.

Run `python -B -O check.py` for the [finite exact checks](CHECKS.txt), and `sha256sum -c SHA256SUMS` for file integrity. The limiting theorem is analytic; the finite checks do not replace the proof.
