# How many thresholds are needed to stop near the cheapest draw?

**Yongxian Zhang · 19 November 2026.** AI-assisted research manuscript, independently reviewed internally by AI, not externally peer-reviewed. No priority guarantee.

A decision maker must buy once from $n$ sequential i.i.d. cost offers. With a known distribution, how many *distinct acceptance thresholds* does the decision maker need to compete with a prophet who knows all the costs? This is the first question in [Livanos and Mehta, SODA 2024, §5, p. 451](https://par.nsf.gov/servlets/purl/10511091). The final offer is forced and does not use a threshold. The results below assume a continuous, nonnegative cost law of positive finite mean with lower endpoint zero.

**A sharp resource transition.** Let $Q$ be the lower quantile and suppose $Q(cu)/Q(u)\to c^r$ at zero, with $r>0$. For each fixed competitive target strictly larger than the unrestricted optimal limiting ratio $\Lambda_r=(1+r)^r/\Gamma(1+r)$, the least number of thresholds needed at horizon $n$ is
$$
\log^* n+O_{F,C}(1).
$$
Here $\log^* n$ counts how many logarithms reduce $n$ to at most one. Any fixed deficit in threshold count below $\log^*n$ still permits a constant factor, depending on the deficit and the law; an unbounded deficit prevents a uniform constant. An unbounded surplus tending to infinity suffices to recover the known unrestricted limiting ratio. The additive uncertainty is not a claim of an exact finite-$n$ threshold count. See [GROWING.md](GROWING.md).

**The exact cost of each fixed budget.** Write $H_k(n)$ and $M_n$ for the best expected online cost with $k$ thresholds and the expected minimum, respectively. For every fixed $k\ge1$, with $\log^{(k)}$ denoting the $k$-fold logarithm,
$$
\frac{H_k(n)}{M_n}\sim
\frac{Q(r\log^{(k)}(n)/n)}{\Gamma(2+r)\,Q(1/n)}\qquad(r>0).
$$
[PROOF.md](PROOF.md) also gives a $k$-step quantile recursion for arbitrary slowly varying lower quantiles ($r=0$). The admissible policies may choose future thresholds adaptively from earlier rejections, provided each threshold is chosen *before* seeing the current offer and the path uses at most $k$ distinct cutoffs. The estimates are not claimed for arbitrary irregular cost laws or for selecting several offers.

**Two single-threshold distinctions.** [EXAMPLES.md](EXAMPLES.md) gives two continuous fixed-law counterexamples within the minimum extreme-value domains used in [Livanos and Mehta, EC 2025](https://par.nsf.gov/servlets/purl/10659245). For every $r>0$ there is a law in $D_{-r}$ for which even the best single-threshold ratio divided by $(\log n)^r$ diverges (Theorem 1.5, p. 1165). There is also one law in $D_0$ for which every fixed finite threshold budget has divergent ratio (Remark 4.1, p. 1174), even though unrestricted stopping attains ratio tending to one. These examples concern **single thresholds**, not the EC theorem for unrestricted optimal stopping. Prior lower bounds using a worst-case law are also not refuted.

[Prior work and source comparison](SOURCES.md) · Internal reviews: [fixed budgets](REVIEW.md), [growing budgets](GROWING-REVIEW.md), [examples](EXAMPLES-REVIEW.md). Run `python3 -B -O check.py` and compare with [CHECKS.txt](CHECKS.txt) for exact finite checks. They verify the block structure and several exact finite identities, not the asymptotics by extrapolation. Run `sha256sum -c SHA256SUMS` to verify the files.
