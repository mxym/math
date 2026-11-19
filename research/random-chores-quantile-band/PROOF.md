# Exactly which fixed iid cost laws admit an envy-free band just below two chores per agent?

AI-assisted research note. The two ingredients are the [rectangular allocation construction](CONSTRUCTION.md) and the [earlier finite-prefix lemma](../random-chores-factor-two/PROOF.md). No external review or priority assertion.

Let F be one fixed atomless distribution function of nonnegative disutilities on [0,1], extended by 1 above 1. Write Q(u)=inf{x∈[0,1]:F(x)≥u} for 0<u<1. Atomlessness gives F(0)=0, continuity, Q(u)>0, and F(Q(u))=u (flat portions of F cause no problem). For each market, all n·m costs are independent with this one law. Every chore must be placed; envy is assessed by comparing sums of costs with other assigned bundles.

Call a **left EF band at 2** the existence of a δ∈(0,1) such that for every deterministic sequence of integer markets n→∞, (2−δ)n≤m<2n, the probability that a complete, exactly envy-free allocation exists tends to 1. This property is one-sided, all sizes in the indicated band, and does not assert a single sharp threshold for the model.

**Dichotomy.** For this fixed F the left EF band property holds if and only if

$$
\limsup_{u\downarrow0}\frac{F(2Q(u))}{u}<\infty. \tag{D}
$$

More precisely:

* If F(2Q(u))≤Du for all sufficiently small u, one can take
  d=24, L=5+3d²=1733 and δ=min{1/(2d), exp(−2DL)/[6(d²+1)]}. The allocations constructed have exactly k=2n−m singleton and n−k doubleton bundles.
* If the limsup is infinite, there is a sequence of chore counts m_j→∞ such that for every fixed 1<c<2, with n_j=⌊m_j/c⌋, the probability of *any* complete EF allocation tends to zero. The law and m_j are chosen once, independently of c; probabilities converge for each fixed c, not uniformly or simultaneously. No claim of failure along every sequence is made.

## Sufficiency: quantile form of the rectangular allocation

Use the A/B construction, exponentially cheap optimal assignments, reserved columns, d matching layers on different n−k-row domains, and purge/resilience proof of [the construction](CONSTRUCTION.md). Only the transfer from exponential ranks to true cost needs replacement. In its notation put

$$
z_i=X_i+d\max_{h:\,i\notin O_h}Y^h_{i,\pi_h(i)}.
$$

The sum and maximum estimates, before applying any cost transformation, give whp

$$
\sum_i z_i\le L,\qquad \max_i z_i\le u_n=C\frac{\log^2 n}{n}
$$

for a sufficiently large fixed C. Both events use only the exposed winning A-minima, the unreserved A matching and B arrays, not the losing entries of reserve columns. As before, actual A-cost is Q(1−exp(−X)) and B-cost is Q(1−exp(−d min_h Y^h)). Their joint iid F marginal is exact.

On that event, n large makes z_i∈(0,1) and within the range of (D)'s bound. Each true own A-cost and each individual B candidate cost is ≤Q(z_i). Thus the personal budget

$$
T_i=2Q(z_i)
$$

covers each eligible one- or two-item bundle. There is no need for Σ T_i to be bounded. Conditional on the exposed data, for a candidate reserve column with owner i each off-owner losing value dominates F, and these values are conditionally independent across cells, as proved in [the construction](CONSTRUCTION.md) §3. The chance this one column is safe is therefore at least

$$
\prod_{j\ne i}(1-F(T_j))\ \ge\ \prod_j(1-Dz_j)\ \ge\ \exp\!\left(-2D\sum_jz_j\right)\ \ge\ \exp(-2DL).
$$

Here Dz_j≤1/2 eventually and the bound on F(2Q(z_j)) holds for every such z_j, not merely along selected quantiles. Conditional independence across the r=⌊n/2⌋ reserve columns gives linearly many safe candidates whp. Select k with disjoint B neighborhoods exactly as before.

For the pair-envy purge set the deterministic threshold τ_n=2Q(u_n). Monotonicity gives max_i T_i≤τ_n; the iid marked bipartite graph now has edge probability F(τ_n)≤Du_n=O(log² n/n). The overlapping-4-cycle argument needs only this bound, not a density or linear scale for the threshold itself. With the unchanged d=24 colored bijections, whp parallel excess ≤1 per vertex, each surviving vertex retains ≥d−3 colors, rectangular Hall provides a perfect matching, and no singleton or pair envy remains. These are exactly [the construction](CONSTRUCTION.md) §§3–5 with the displayed budget and threshold substitutions. Outside the high-probability budget event one can stop without constructing an allocation; Q need never be evaluated at an argument exceeding 1.

## Necessity: nondoubling supplies the earlier certified-prefix obstruction

Choose u_j↓0 with v_j=F(2Q(u_j)) satisfying v_j/u_j→∞. Set x_j=Q(u_j)>0 and m_j=⌊1/√(u_jv_j)⌋. Since u_j→0 and v_j≤1, m_j→∞ (pass to a strictly increasing subsequence if desired),

$$
m_ju_j\longrightarrow 0,\qquad m_jv_j\longrightarrow\infty.
$$

Indeed m_j u_j≤√(u_j/v_j), and m_j v_j≥√(v_j/u_j)−v_j. The formula works even for a positive lower endpoint, when v_j may stay bounded away from zero.

For one agent with m_j iid draws the probability of any cost at most x_j is at most m_jF(x_j)=m_j u_j→0. The number in (x_j,2x_j) is binomial with mean m_j(v_j−u_j)→∞ and variance at most that mean; equality of the interval mass uses atomlessness at both endpoints, including at 1 if relevant. Hence for every fixed K at least K costs are there with probability tending to one. On the intersection, the first K costs are <2x_j while the two cheapest distinct chores have cost sum >2x_j. Thus this is a certified ordered K-prefix in the precise sense of the earlier note [Random additive chores, §§1–3](https://github.com/mxym/math/blob/45e49af8f0271d64eac7a3a7b6c4a028d34d71aa/research/random-chores-factor-two/PROOF.md). Eligibility uses only order statistics; the random ordering of labels is independent, uniform, and different rows are independent.

For clarity, that earlier result is used as an existing lemma, not a contribution of the present converse. At fixed c∈(1,2) set n_j=⌊m_j/c⌋, fix ρ=9/10, and use the fixed K=K(c) and fixed number of rounds t=t(c) in its §3. The eligibility probability γ_j tends to one, so eventually independently thin eligible rows with conditional probability ρ/γ_j. Their K-lists are then independent uniform lists at Bernoulli(ρ) retained rows. Requests grant unique ownership of a requested chore if singleton; two requests certify a nonsingleton. The earlier finite-depth proof gives the limiting fraction of double-requested items via λ_{s+1}=(ρ/c)∑_{i=0}^{K−1}p_s^i, p_{s+1}=1−e^(−λ_{s+1}), p_0=0; at the fixed t its value 1−(1+λ_t)e^(−λ_t) strictly exceeds 2(1−1/c). Briefly, as K→∞ at each fixed depth the limiting update is λ=(ρ/c)/(1−p); there is no fixed point below p=1 since ρ/c>1/e. A fixed t and then sufficiently large fixed K give the strict margin. But in any complete EF assignment with m<2n, no bundle is empty and at most 2(m−n) chores lie in nonsingleton bundles. The earlier lemma therefore rules out EF whp. Its use requires no regularity or further conditions on F beyond the certified independent retained lists. The auxiliary thinning shows failure of existence for the original market since under any realization the certificates are sound.

For any purported δ>0 choose a **fixed** c∈(max(1,2−δ),2). Eventually (2−δ)n_j≤m_j<2n_j. Failure along the sequence contradicts a left EF band, completing both directions.

## Examples and boundaries

A two-sided local linear CDF (in particular a fixed globally PDF-bounded law) has (D), since for small u, Q(u)≤u/a and F(2Q(u))≤(2b/a)u. The direct linear-CDF proof in [the construction](CONSTRUCTION.md) gives a slightly sharper explicit constant for this subclass. For a fixed regularly varying CDF at zero of positive finite index s, F(2x)/F(x)→2^s, Q(u)→0 and F(Q(u))=u, so (D) holds without requiring a positive finite density at zero. If the support has positive lower endpoint, then F(2Q(u)) is bounded below by a positive constant for small u; (D) fails. The CDF F(x)=exp(1−1/x), 0<x≤1, is a nondoubling example with lower endpoint zero since F(2x)/F(x)=exp(1/(2x)) for x≤1/2.

This does not identify actual threshold constants (even for uniform costs), prove anything about every m≥2n for all atomless F, or contradict the earlier worst-case example where the PDF-bounded law is allowed to change as c↑2. All references to existence include all chores; nothing is discarded.
