# How often does the last uncovered planar disk shrink?

Take nested independent uniform samples in a compact planar domain of area a and perimeter P, with C¹,¹ boundary. A record is a strict decrease of the radius required to cover the whole domain at least k times. For every fixed k, the number of records through sample size n is asymptotic almost surely, and in expectation, to cₖ(log n)²/2. The time of the jth record raised to the power 1/√j tends almost surely to exp(√(2/cₖ)).

* For k ≥ 2, cₖ = 1/2.
* For k = 1, c₁ = (1+p)/2, where p is the integral of exp(−t−P√(t/(πa))) over 0 < t < ∞. This p is the probability the *interior*, rather than the boundary, wins in the limiting one-time competition.

This answers the **uniform planar, full-domain** conjecture immediately after [Penrose, Theorem 2.3](https://arxiv.org/html/2608.19104v3#S2), not the more general tied-density question. The corresponding one-time radius laws and the martingale approach to records are prior results. The proof identifies the winning disk's mass and controls its switching along one nested sequence rather than inferring a frequency from a single-time limit.

[Proof](PROOF.md) · [Primary-source comparisons and search limits](SOURCES.md) · [Independent internal mathematical review](REVIEW.md). Checksums are in [SHA256SUMS](SHA256SUMS). AI-assisted research, with a second internal AI proof review; neither external peer review nor a priority certification.
