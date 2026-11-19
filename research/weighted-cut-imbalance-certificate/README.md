# The weighted Max-Cut conjecture for one-round binary feedback

For any finite graph with nonnegative edge weights, write $W$ for total edge weight, $C$ for the maximum cut, and $d_i$ for the weighted degree of vertex $i$. This computer-assisted proof establishes
$$ C\ \ge\ \frac25 W+\frac4{15}\,\mathbb E\left|\sum_i d_i\epsilon_i\right|, $$
where the signs are independent and uniform. This is the **full weighted conjecture** of [Braverman, Efremenko, Kol, Saxena and Zhang (ITCS 2025, Conjecture 3)](https://doi.org/10.4230/LIPIcs.ITCS.2025.22), not a bounded-order, bounded-color or equal-weight case.

**Implication for communication.** In the authors' adversarial binary corruption model with one noiseless feedback round, the optimal asymptotic error-resilience **supremum** is $7/23$. For every fixed $0<\varepsilon<7/23$, a constant rate depending on $\varepsilon$ suffices at resilience $7/23-\varepsilon$. Their theorems supplied the upper bound and proved this implication from the graph conjecture; this note proves the missing graph inequality. It does not claim a constant positive rate at the exact endpoint or construct a new coding protocol.

**Why a finite computation covers arbitrarily large graphs.** Normalize edge weight to one. Fix the largest degree and the maximum cut. For each $2\le k\le31$, a cut that separates the top vertex, randomly splits the next $k-1$ vertices, and randomly colors the rest gives linear bounds on the sum of the $k$ largest degrees. On each of 957 polygons in the two-parameter plane, a single collection of these bounds holds at every point. At each corner, the certificate exhibits a 32-coordinate vector whose partial sums dominate all the degree bounds; interpolation and convexity prove the inequality throughout the polygon. Every longer prefix is covered because the comparison vector already has total mass 2 at coordinate 32 and the **entire** degree vector of any graph sums to 2. No actual nonzero degree is discarded.

**How to inspect the result.**

- [Mathematical proof and certificate format](PROOF.md); [sources and prior cases](SOURCES.md).
- [Rational certificate](certificate.json); [first verifier](verify.py) and [independently implemented verifier](independent.py). Both use only Python's standard library; no LP solver, external data, random samples or floating-point threshold checks are required.
- [Completed runs](CHECKS.txt); [independent internal review](REVIEW.md); [SHA-256 hashes](SHA256SUMS).

From this folder run:

    sha256sum -c SHA256SUMS
    python3 -B -O verify.py certificate.json
    python3 -B -O independent.py certificate.json

The equally weighted triangle and five-clique were already known equality examples. No classification of equality, and no result for BEKSZ's separate Conjecture 1.5, is claimed. This is AI-assisted research with internal review and exact arithmetic, not external peer review or a proof-assistant formalization. Historical priority is not guaranteed.
