# When is an equal split of flexibility optimal in a two-sided matching market?

**Yongxian Zhang (张永贤) · AI-assisted research draft · November 2026.** Independently checked in a separate internal AI derivation; not externally peer-reviewed. No claim of worldwide priority.

A platform can make a fixed fraction of the two sides of a matching market more flexible. A flexible agent has more potential partners, but making an agent flexible does not guarantee a particular match. In the sparse, independent-edge model of [Freund, Martin and Zhao](https://arxiv.org/abs/2404.04709), we prove:

**For every fixed positive regular connection rate and every fixed partial budget, splitting the budget equally is the unique optimal allocation once the flexible connection rate is sufficiently large.** The comparison is with every feasible split, not just assigning the whole budget to one side.

The objective is the *large-market* expected maximum matching size divided by the number of agents on one side. First let the market size tend to infinity for each fixed pair of rates. For each fixed regular rate α>0 and budget 0<B<1, there is then a finite threshold f₀(α,B) after which the conclusion holds. We do not compute f₀, settle all parameter regimes, or obtain an exact finite-population optimizer.

- [The limiting curve and its possible plateau](CURVE.md). As the flexible rate tends to infinity, the unmatched fraction is the positive part of an even, strictly convex function of imbalance. Depending on the parameters, several nearby splits can all approach a matching rate of one.
- [Why equal division nevertheless wins at finite high rates](FINITE.md). Maximizing pairs in the established variational formula yield strictly convex trial functions, directly or after swapping the two sides. This distinguishes the finite-rate optimizer even when the limiting curve cannot.
- [Shorter proof for the two canonical splits](ENDPOINT.md). At high flexibility the equal split strictly beats placing the entire budget on one side, including the parameter range left undetermined after Theorems 4–5 of [Ameen, Sentenac and Yu](https://arxiv.org/html/2604.02295v2).
- [Sources and overlap](SOURCES.md); [independent internal mathematical review](REVIEW.md). The random-graph matching formula is a theorem of Ameen, Sentenac and Yu, not a contribution of this note.

To replay exact algebraic checks and illustrative rigorous bounds on global scalar maxima, run `python3 -O verify.py` (standard library) and compare with [CHECKS.txt](CHECKS.txt). The general result follows from the proofs, not from testing examples. `sha256sum -c SHA256SUMS` checks the package. The title-line notices and cross-reference between the two proof files were edited after review; their mathematical arguments are unchanged.
