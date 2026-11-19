# The drawn length of a critical beta-splitting cladogram is linear

**Yongxian Zhang.** Put every leaf at level zero and draw each branch point one level above its higher child. Aldous and Janson proposed that the expected total vertical length of this drawing grows like n(log n)⁴. Instead it is asymptotic to cn, with an explicit convergent series for c in terms of finite-tree height laws.

In fact the number of vertical edges crossing each level, divided by n, has a deterministic limiting profile. The error summed over **all levels** tends to zero in every fixed finite Lᵖ. This addresses the normalized profile, not its fluctuations. The proof counts edges by the heights of the descendant trees below the branch points. It uses existing results for the maximum height and the frequencies of fixed subtrees; it is not a new theorem about maximum height, correlations between leaves, or continuous branch lengths.

* [Proof, limits and definitions](PROOF.md)
* [Original open problems, established inputs and prior comparison](SOURCES.md)
* [Independent internal review](REVIEW.md). AI-assisted research and checking; no external peer review or guarantee of priority.
* Run `python -B -O check.py` to reproduce the [finite exact checks](CHECKS.txt), and `sha256sum -c SHA256SUMS` to check file integrity. These tests are not a substitute for the asymptotic argument.
