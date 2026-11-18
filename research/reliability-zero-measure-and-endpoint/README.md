# Where the zeros of graph reliability polynomials concentrate

Two questions about independent edge failures have different answers: **where do most roots lie**, and **how close can a negative real root of a complete graph get to −1**?

- **The full zero measure.** For any sequence of finite connected simple graphs, with at least two vertices each, the zero-counting measures converge weakly to uniform arclength on the unit circle **if and only if** the average degrees tend to infinity. Count multiplicity and retain the root at 1. In particular this answers the unnumbered measure question after [Buys's Question 4.1](https://arxiv.org/html/2604.07541v1#S4.SS1). It does **not** prove the individual-root containment asked for in numbered Question 4.1.
- **The negative endpoint for complete graphs.** For each order $n\ge3$ congruent to $0$ or $3\bmod 4$, $K_n$ has a real reliability root in $(-1,0)$. Along **any** sequence of orders tending to infinity for which such roots are chosen, $1+q_n\sim 2\log(n)/n$. The congruence classes guarantee existence; the rate applies to every choice of these negative real roots, not to all complex roots. The principal quantitative point is the constant 2: the existence statement and qualitative convergence already follow by combining the classical endpoint sign with Buys's fixed-disk convergence. This addresses [Omar's request for an explicit family and a rate](https://arxiv.org/html/2604.03530v1#S4), not the best possible rate among all simple graphs.

Here $q$ is the **failure**, not retention, probability for each edge. Using retention $p=1-q$ shifts the limiting circle to the one centered at 1.

[Proof](PROOF.md) · [Sources, scope and comparison with prior work](SOURCES.md) · [Internal review and finite checks](CHECKS.md).

**Status.** AI-assisted research draft, independently re-derived within the same AI-assisted workflow. Not externally refereed or formally verified. No claim of exhaustive priority, DOI, or release. Sources are cited, not reproduced; third-party rights are unchanged.
