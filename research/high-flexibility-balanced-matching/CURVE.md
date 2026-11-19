# The whole high-flexibility allocation curve in two-sided random matching markets

Yongxian Zhang. AI-assisted research draft, not externally peer-reviewed. Notation and inputs: the independent-edge balanced two-class bipartite matching model of Freund–Martin–Zhao (FMZ, arXiv:2404.04709v3) and Ameen–Sentenac–Yu (ASY, arXiv:2604.02295v2, Theorem 1, Corollary 1). Fix a regular rate α>0 and total budget 0<B<1. Write c=2α, s=1−B/2 and −B/2≤δ≤B/2. The fractions of **regular** agents on the two sides are p=s−δ and q=s+δ; the flexibility fractions are (1−p,1−q). Both sides have n agents, types are independent, and the given types connect independently at rates c/n between regulars, (α+f)/n between distinct types, and 2f/n between flexibles. For each fixed f take n→∞ first, and let η_f(δ) denote the limiting expected matching cardinality divided by n. Then take f→∞, which is not a simultaneous n,f limit.

**Theorem.** Let h(y)=y(1−log y) for y>0 and h(0)=0, and define

    H(δ) = max_{0≤y≤1} G_δ(y),    G_δ(y)=p exp(−c q y)+q h(y)−1.

The high-flexibility unmatched rate is U(δ)=lim_{f→∞} [1−η_f(δ)]=max(0,H(δ)). The convergence is uniform in δ on this interval for *fixed* α,B. H is continuous, even and strictly convex and strictly increases with |δ|. In particular balance is optimal in the limiting model. If H(0)≥0 it is uniquely optimal; if H(0)<0 there is a unique δ_*∈(0,B/2) with H(δ_*)=0, and exactly |δ|≤δ_* achieve limiting matching rate one. Beyond this plateau the limiting matching rate strictly decreases with |δ|. The one-sided endpoint has strictly worse limiting matching rate than balance for all these α,B, hence is strictly worse at all sufficiently large finite f for each fixed α,B. This limit argument alone does not establish an exact optimizer at large finite f. [The companion proof](FINITE.md) does so by an additional argument; the unrestricted finite-rate phase diagram is not determined.

## 1. Limit for every split

For interior δ, p,q∈(0,1). The total incoming rates at right types are M₁=pc+(1−p)(α+f), M₂=p(α+f)+(1−p)2f. They both go to infinity. Change variables y=exp(−M₁t₁), z=exp(−M₂t₂) in ASY Theorem 1; by Corollary 1 the unmatched fraction is the maximum over D_f=[exp(−M₁),1] × [exp(−M₂),1] of

    p exp[−c q y−(α+f)(1−q)z]
    +(1−p) exp[−(α+f)q y−2f(1−q)z]
    +q h(y)+(1−q)h(z)−1.                                    (1)

This uses ASY's variational formula, not a heuristic branch of a fixed-point iteration. The following limiting argument adapts ASY Appendix C.2 (their p=q case).

For any fixed y>0 choose z=exp(−M₂) in D_f for all sufficiently large f. Since f z→0, (1) tends to G_δ(y). At (1,1) the objective tends to 0, as f(1−q)→∞. By continuity of G_δ at 0 this gives liminf ≥max(0,H(δ)). For the upper bound take any f_j→∞ and any subsequence attaining the limsup, then convergent maximizers with limits (u,v)∈[0,1]². If v>0 both exponentials vanish and the upper limit is at most zero because h≤1. If v=0 and u>0 the second exponential vanishes and the first is bounded above by p exp(−c q y); hence the upper limit is at most G_δ(u). If v=u=0 both h terms vanish and the exponentials are at most their weights (which sum to one), so the upper limit is at most zero. This proves the formula for all interior splits.

At δ=B/2 the regular masses are (1−B,1). ASY Proposition 3 directly gives the untruncated maximum H(δ); it is strictly positive since the trial y=1 gives (1−B)exp(−c). For the transposed endpoint use invariance of the matching problem under exchanging the two sides and the equality H(−δ)=H(δ) proved next **solely from the scalar objective**, including the endpoints. There is no application of the interior argument at q=1, where the flexible-right term is absent. The balanced case agrees exactly with ASY Proposition 4.

## 2. Evenness, strict convexity and truncation

For all allowed δ one has p,q≥1−B>0. G_δ is continuous on [0,1]. Its y derivative q[−cp exp(−c q y)−log y] tends to +∞ at 0 and is negative at 1; thus each maximizer lies in (0,1). Choose such a y and put x=exp(−c q y). Criticality implies y=exp(−c p x). Consequently

    G_δ(y)=p x+q y+c p q x y−1=G_{−δ}(x).

The right is a feasible trial for H(−δ); hence H(−δ)≥H(δ). Reversing δ yields equality. This is valid without uniqueness of critical points or differentiability of H.

For any fixed y>0, the second derivative in δ of G_δ(y) is

    exp(−c q y) [2cy + p(cy)²] > 0.

To see strict convexity passes to the maximum (not automatic in some infinite families), choose an interior-in-y maximizer at a strict convex combination δ₀ of two different δ values. For that specific y, apply its strict Jensen inequality at those two parameters, then bound the two endpoint values by their maxima. Thus H is strictly convex on the whole closed interval. Its continuity also follows from joint continuity on the compact rectangle. An even strictly convex function strictly increases on positive distances from zero, as any smaller nonnegative point is a strict convex combination of ± the larger point. This proves monotonicity and, using continuity and H(B/2)>0, proves all plateau, uniqueness, and strict comparison assertions. If H(0)=0 the singleton {0} is the only split with limit one, not a positive-width plateau.

## 3. Uniform convergence (not a finite-rate optimizer claim)

For each fixed f>α, ASY's original formula over [0,1]² is continuous in δ: before the change of variables (t₁,t₂) are on a fixed compact domain and the objective is jointly continuous in δ and t, including vanishing class proportions. Each finite-n model can be coupled for two fixed f values by the same types and same independent uniforms on edges, so maximum matching is nondecreasing with f. Apply this for n large enough that all probabilities in the two models lie in [0,1], then take n→∞. Therefore [1−η_f(δ)] decreases to the proved continuous function U(δ). Dini's theorem for any integer sequence f→∞ gives uniform convergence on the compact split interval; monotonicity sandwiches all real f. In particular any subsequential limit of maximizing splits for growing f maximizes the limiting matching rate; a strict ordering for a fixed pair of limiting values persists eventually. This does not select points within a limiting plateau or resolve finer finite-rate ties.

**Attribution and boundary.** ASY already derive the two endpoint limits as Propositions 3–4, prove a substantial part of their strict eventual comparison as Theorems 4–5, and base their limiting proofs on exactly the compactness method adapted here. FMZ originally formulate the two-sided flexibility design problem and prove other comparisons; their concluding question optimizes over all splits at finite connection rates, not just the additional high-flexibility limit. The fresh claims here are explicitly conditional on the established variational theorem, and address the high-flexibility limit and the open eventual endpoint comparison, not the whole finite-rate design problem.
