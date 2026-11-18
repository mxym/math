# A smaller parameter for the split-graph counterexample

The [original proof](../PROOF.md) uses the affine plane over the field of order $2^{40}$. The **same graph construction** works with $q=2^{14}$, giving

$$
 b=q^2=268{,}435{,}456,\qquad N=14b+6bq=26{,}392{,}037{,}163{,}008.
$$

Its ordinary, total and connected dominating-set sequences are each nonunimodal. This appendix changes only estimates and parameters, not the main proof, graph mechanism, or any conjectural conclusion. This is still a graph with more than 26 trillion vertices. We make no smallest-known or minimality claim, and its coefficient sequences were not enumerated.

Use the notation of [the proof](../PROOF.md): $U,V$ are the sets of positions with a missed group on the two sides, $u=|U|$, $v=|V|$, and $w=(63/128)^b$ is the probability of either pure phase. Take $\delta=1/64$ and window radius $r=b/16$.

**Mixed-phase mass.** If the missed group pattern is fixed on one side, every group at a reached opposite position has at least one missed neighbor. An opposite group of size $k$ therefore contributes a factor at most $1-2^{-k-1}$ to the conditional domination probability. The products for the two types of position (group sizes $(1,6)$ or $(2,2,3)$) are $381/512$ and $735/1024$. Each is strictly less than $2^{-2/5}$ by taking fifth powers. Consequently the conditional probability is at most $2^{-2|\Gamma(U)|/5}$. Each exact missed pattern on the fixed side has probability at most $w$ (each missed-to-hit odds ratio is at most one). The following mass bounds are divided by $w$:

1. If $1\le u\le q$, then $|\Gamma(U)|\ge qu/2$. Bounding the number of patterns by $(7b)^u$, the geometric sum has ratio $7b\,2^{-q/5}<2^{-12}$, hence sums to less than $1/4095$.
2. If $q<u\le\delta b$, then $|\Gamma(U)|\ge b/2$. With $t=1/448$, the sum of $\binom bu7^u$ up to $\delta b$ is at most $t^{-\delta b}(1+7t)^b = 448^{b/64}(65/64)^b<2^{11b/64}$: use $448<512$ and $(65/64)^{64}<4$. The conditional factor $2^{-b/5}$ reduces the bound to $2^{-9b/320}$. Bounds 1 and 2 apply to either side.
3. If $u,v>\delta b$, the error term in [incidence estimate (3)](../PROOF.md) is at most $1/(\delta\sqrt q)=1/2$ times its leading term. The number of forced auxiliaries is at least $uv/(2q)\ge \delta^2 qb/2=2b$. Therefore the *unconditional* mass on this range is at most $2^{-2b}$, and its ratio to $w$ is below $2^{-b/2}$ since $(63/128)^2>1/8$.

Both power tails are less than $1/4096$. The mixed ordinary-dominating mass divided by $w$ is thus less than $2(1/4095+1/4096)+1/4096<1/100$.

**Strict valley.** Each phase variance is at most $2bq$, so Chebyshev's bound on the probability of missing its own window is $2bq/r^2=1/32$. Consecutive window centers are $b/6>2r$ apart. For any of the three families, each outer window therefore has mass at least $31w/32$, while the middle window has mass at most $(1/16+1/100)w$. The lower bound for an outer peak divided by the upper bound for the middle trough is at least

$$
\frac{(31/32)/(2r+1)}{(1/16+1/100)/(2r-1)}
=\frac{26{,}004{,}684{,}025}{1{,}946{,}157{,}114}>13.
$$

In particular the trough is strictly below both peaks. The indices can differ between families, exactly as in the original argument.

**Exact replay.** Run `python3 -B -O check.py` and `sha256sum -c SHA256SUMS` here. The standard-library checker verifies the scalar inequalities with integers and fractions, and prints the three disjoint integer windows. It does not enumerate the graph or its coefficients. The derivation and separate check were AI-assisted, not external peer review. The [original sources and scope](../SOURCES.md) are unchanged.
