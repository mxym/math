# Recovering the unique farthest target point from a gradient

Fix a nonempty compact set B in finite-dimensional Euclidean space, independent of the locations of n random sites (in particular B may be deterministic). Suppose the sites have a joint density; they need not be independent or identically distributed. For each 1 ≤ k ≤ n let Rₖ be the maximum over b ∈ B of its kth smallest site distance, counting multiplicity. Almost surely, simultaneously for all k:

1. Rₖ > 0 and exactly one bₖ ∈ B attains it.
2. Its open ball of radius Rₖ contains exactly k−1 sites. In particular R₁ < ⋯ < Rₙ.
3. For a new independent absolutely continuous site of law μ, conditional on the old sites and B, the probability of a strict decrease at multiplicity k is exactly μ of that open ball (with B deterministic, or independent of the entire sample including the new site).

No convexity, smooth boundary, positive target volume, large n or small radius is imposed. This strengthens the covering-threshold portion of [Penrose v3, §5, Propositions 5.1–5.2](https://arxiv.org/html/2608.19104v3#S5); it is not about a ball required to be contained in the target, nor all radii in the *location-dependent* admissible regions of maximal spacings.

## Proof

Condition on a fixed B and write Φ(X) for the kth covering radius as a function of the vector X=(x₁,…,xₙ) of sites. By the triangle inequality every individual distance is Lipschitz under site perturbations with common modulus maxᵢ|Δxᵢ|. Taking an order statistic, then a maximum, preserves this modulus. Rademacher's theorem gives differentiability at Lebesgue-almost every configuration. Fix such a configuration with R=Φ(X)>0 (for absolute continuity, distance from any single fixed point of B to every site is positive almost surely). Write G=(G₁,…,Gₙ) for the gradient in the site variables.

For **every** maximizing b, its active index set I={i:|xᵢ−b|=R} is nonempty. Let q be the number of distances strictly below R. Under a one-sided displacement D=(D₁,…,Dₙ), the directional derivative of the kth distance **at this fixed b** is the (k−q)th smallest among the numbers uᵢ·Dᵢ, i ∈ I, where uᵢ=(xᵢ−b)/R. Indeed, finitely many inactive distances stay on their original sides for sufficiently small displacements; all active distances have these first-order expansions, and the order statistic is Lipschitz. Since Φ after displacement is at least the value at b and equality holds before displacement,
$$
 G\cdot D \ \ge\ \min_{i\in I} u_i\cdot D_i \qquad\text{for every }D.
$$
Finite-dimensional convex separation says G belongs to the convex hull of the block vectors whose only nonzero block is uᵢ in position i, over i ∈ I. Equivalently, there are nonnegative weights tᵢ summing to one such that Gᵢ=tᵢuᵢ for i ∈ I and Gᵢ=0 off I. In particular Σᵢ|Gᵢ|=1. Choose any index with Gᵢ≠0: then b=xᵢ−RGᵢ/|Gᵢ|. The right-hand side depends only on the configuration and k, not the chosen maximizer. This proves uniqueness.

If q < k−1, the (k−q)th smallest active directional derivative is nonnegative whenever only one site moves: at most one of its entries can be negative. Testing both signs of every individual block displacement in the preceding first-order comparison gives Gᵢ=0 for every i. This is impossible. Hence q=k−1. Intersect the resulting full-measure sets for the finitely many k. If adjacent maximal radii were equal, the winner at k would also attain that value for k+1 by monotonicity of site order statistics and maximality. Its open ball would have to contain both k−1 and k sites, an impossibility.

A new site outside or on the winning sphere cannot reduce the old value at the winner. A site strictly inside brings the number strictly inside to k, strictly improving that target. All other target values were strictly below the old maximum and cannot increase. The updated continuous order-statistic function attains a maximum on compact B, so its new maximum is strictly smaller. This proves the conditional assertion.

## Bounds on the scope

The same proof works with a fixed strictly convex norm, even if the norm is not differentiable everywhere. At each active difference select a norming covector pᵢ of dual norm one. Convexity gives the one-sided bound by pᵢ·Dᵢ; after taking the order statistic, the derivative of Φ therefore dominates the corresponding (k−q)th order statistic of these linear lower bounds. Separation again gives Gᵢ=tᵢpᵢ and the sum of dual norms one. Any Gᵢ≠0 exposes a *unique* unit vector in the primal ball by strict convexity and compactness; it must be (xᵢ−b)/R. The same q and record conclusions follow. Strict convexity cannot simply be discarded for all norms: with the maximum norm on the plane, one random site in a small open disk about the origin and target the segment {(2,t): |t|≤1/2}, every target point has the same site distance.

For Euclidean distance the argument also shows that Rₖ has an absolutely continuous law: the site gradient has norm ≥1/√n almost everywhere on Φ>0. The coarea formula applied on bounded coordinate boxes shows the inverse image of a Lebesgue null set of radius values is null up to configurations of radius zero, already excluded. This distributional assertion is also obtainable from direct local level-band estimates; no bounded-density claim for arbitrary site laws is implied.
