# The weighted degree-square Max-Cut conjecture to first order

Let $C$ be the maximum cut of a finite loopless graph of positive total edge weight $W$ with nonnegative weights, and put $p_i=d_i/(2W)$, $P=\sum_i p_i^2$. For **every** such graph,
$$
\frac CW-\frac12\ \ge\ \frac{P}{2(1+2\sqrt P)}.
$$
Thus for any sequence with $P\to0$, the lower bound is $(1-o(1))P/2$ regardless of graph order or degree heterogeneity. The short proof applies a deterministic cut constraint to recentered independent signs and averages it before dividing.

The [Braverman–Efremenko–Kol–Saxena–Zhang conjecture](https://doi.org/10.4230/LIPIcs.ITCS.2025.22) asks for the **larger** bound $P/2$ for each graph. That exact conjecture remains unproved here. The odd-clique examples and the near-uniform $(nP\to1)$ leading case were known. No optimal graph error order, feedback-channel result, or priority is claimed.

- [Proof](PROOF.md) and [source comparisons](SOURCES.md).
- [Independent internal review](REVIEW.md), including an alternative proof based on moving vertices of the heavier side.
- The two standard-library scripts check finite examples with exact arithmetic, not in lieu of the all-order proof. Run:
  ```sh
  python3 -B -O verify.py
  python3 -B -O independent.py
  sha256sum -c SHA256SUMS
  ```
  Compare with [author replay](AUTHOR-CHECKS.txt) and [independent replay](INDEPENDENT-CHECKS.txt).

AI-assisted research draft with independent internal AI review; not externally peer-reviewed.
