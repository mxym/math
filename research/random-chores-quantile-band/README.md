# Which cost distributions permit envy-free chore allocation just below two chores per agent?

Fix an atomless cost law on $[0,1]$. Each of $n$ agents independently draws a cost for each of $m$ chores from this law, adds the costs of a bundle, and must receive a bundle in a complete allocation. No goods, subsidies, discarded chores or relaxed notion of envy are involved.

**Criterion.** Write $F$ for the cost distribution function (extended by 1 above 1) and $Q$ for its lower quantile. There is a constant $\delta>0$ such that **every** size sequence $(2-\delta)n\le m<2n$ admits an envy-free allocation with probability tending to one if and only if

$$
\limsup_{u\downarrow 0}\frac{F(2Q(u))}{u}<\infty.
$$

This compares the fraction of chores cheaper than a low quantile with the fraction cheaper than twice that cost. When this fraction increases by at most a fixed factor, a construction gives exactly $2n-m$ singleton bundles and $m-n$ pairs. If the factor is unbounded, a common sequence of chore counts defeats **each fixed** ratio $1<c<2$ along $n=\lfloor m/c\rfloor$. This does not say every size sequence fails.

* **Uniform or power-law lower tails:** satisfy the criterion. The guaranteed band has positive width, but the explicit bound is exceedingly small; it is not the true threshold.
* **Costs bounded away from zero, or $F(x)=e^{1-1/x}$ on $(0,1]$:** fail the criterion. The latter example has costs arbitrarily close to zero.
* **Why this differs from prior work:** [Manurangsi–Suksompong](https://epubs.siam.org/doi/full/10.1137/25M180161X) prove existence for $m\ge2n$ under global density bounds. [The earlier repository obstruction](../random-chores-factor-two/PROOF.md) shows there is no one smaller sufficient coefficient for *all* such laws; [a later note](../random-chores-natural-lower-bounds/PROOF.md) gives lower obstructions. The criterion fixes the law first. It neither locates an exact ratio for that law nor proves existence above $2n$ for arbitrary atomless $F$.

Read [the characterization](PROOF.md), then [the reserved-singleton and rectangular-matching construction](CONSTRUCTION.md). [Sources and scope](SOURCES.md) separates the new argument from the earlier finite-prefix obstruction, assignments and four-cycle pruning. [Review of the construction](CONSTRUCTION-REVIEW.md) and [review of both directions](REVIEW.md) are AI internal reviews, not external refereeing. The quantile-budget extension was proposed during internal AI review and rechecked by another AI. Historical priority is not guaranteed.

**Reproduction.** Python 3 standard library only. The scripts check finite implications and examples, not the asymptotic theorem by simulation:

~~~sh
sha256sum -c SHA256SUMS
python -O verify.py
python -O linear_checks.py
python -O dichotomy_checks.py
python -O linear_independent.py
python -O dichotomy_independent.py
~~~
