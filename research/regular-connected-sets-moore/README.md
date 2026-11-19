# Connected sets in regular graphs: the large-degree rate and a Moore counterexample

Cambie, Goedgebeur and Jooken [asked two questions](https://doi.org/10.37236/12625): do Moore graphs maximize the exponential base of the number of connected vertex sets (Conjecture 2), and is the large-degree deficit from 2 of order $2^{-d}$ (§6)? This note gives a negative answer to both.

- **At the same order:** the incidence graph of the projective plane over $\mathbb F_{2^{14}}$ is a girth-six Moore graph of degree 16,385 and order 536,903,682. We construct a bipartite regular graph of exactly that degree and order whose *connected dominating* vertex subsets already outnumber *all connected* vertex subsets of the Moore graph. The construction applies at every sufficiently large power-of-two plane order, not only this example.
- **At greater orders:** for every sufficiently large prime-power plane order there are arbitrarily large competitors of the same degree with strictly greater per-vertex exponential base. An explicit degree-8,192 comparison needs no matching completion.
- **As the degree grows:** for the extremal connected-set base $c_d$ and connected-dominating-set base $\widetilde c_d$, both $2-c_d$ and $2-\widetilde c_d$ have order $2^{-d}/d$. The constructive estimate comes from independent fibers over a strip of width four. A classical projection bound supplies the reverse inequality.

The graph order tends to infinity at **fixed degree** in the definitions of the bases; only then does the degree tend to infinity. The finite Moore comparisons use direct bounds on named graphs. They do not compare the two unknown maxima at their different orders. No leading asymptotic constant, smallest counterexample or exact base for small degrees is claimed. Conjecture 2 is about connected sets, not connected domination.

**Proof:** [rate and construction](RATE.md) → [Moore comparison and larger example](MOORE.md) → [same-order construction](SAME-ORDER.md). [Sources and scope](SOURCES.md) distinguishes the upper bound, product facts, and earlier constructions.

**Checks:** run `python3 -O check.py` and `python3 -O check_moore.py` (standard library) and compare with [CHECKS.txt](CHECKS.txt) and [MOORE-CHECKS.txt](MOORE-CHECKS.txt). Run `sha256sum -c SHA256SUMS` to check the pinned files. The scripts verify finite cases and the arithmetic of the inequalities; they are not exhaustive counts on the two large graphs.

This is an AI-assisted research note with separate internal AI checking. It has not been externally peer-reviewed or formally verified. The cited authors retain the rights to their work. A search that did not locate a previous solution is not a priority guarantee.
