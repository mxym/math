# Sharp open 60-degree cap occupancies for every irreducible simply-laced root system

Take a reduced irreducible simply-laced root system Φ in its real span, scaled to root squared length two. For any x of squared length two set b(x)=|{r∈Φ : x·r>1}|. The maximum is over **all** cap centers; the minimum column excludes centers that are themselves roots. These are strict, not closed, angular caps.

| type | maximum of b | minimum at a nonroot |
|:---|:---|:---|
|A₁|1|no nonroot center in its span|
|Aₙ₋₁, n≥3|max{n−1, 2(n−2), 3 min(n−3,5)}|2 if 3≤n≤7; 0 otherwise|
|Dₙ, n≥4|max{2n−2, binom(min(n,7),2)}|3 if n≤7; 0 otherwise|
|E₆|16|5|
|E₇|27|6|
|E₈|29|8|

The D row is proved in the [all-rank D theorem](RootDnCapMultiplicities.md). The exceptional minima are the [previous sharp covering multiplicities](KissingExceptionalRootCoverBranch.md); E6's maximum was also proved [previously](KissingE6GlobalMaskCapacity.md). The A row and the exceptional maximum checks are given below. This is a complete extremal calculation for these specified configurations, not a claim about general optimal kissing configurations.

## A: reduce to a bipartite graph with nested neighborhoods

Use the roots eᵢ−eⱼ in the sum-zero hyperplane of Rⁿ. A blocker is exactly an ordered pair with xᵢ−xⱼ>1. Coordinate spread is ≤2 by Cauchy–Schwarz. Cut at the midpoint of the maximum and minimum: strict pairs must run from one side to the other, since the width of each half is at most one. Assign midpoint coordinates arbitrarily to either side; they cannot contribute a strict pair. Sorting the two sides by distance from the midpoint gives a bipartite graph with nested neighborhoods: row lengths r₁≥⋯≥rₐ in a rectangle with b columns, and row i uses its first rᵢ columns.

There cannot be a matching of size four: each disjoint inequality (xᵢ−xⱼ)²>1 costs xᵢ²+xⱼ²>1/2. Nor can there be a K₃,₆: summing its 18 strict differences gives a linear form with squared coefficient norm 3·6²+6·3², hence ‖x‖²>2. In general nonnegative edge weights whose sum is S and vertex degrees (weighted incidences) are dᵥ exclude a graph whenever S>0 and S²≥2Σdᵥ². The signs in the coefficient vector are positive on one shore and negative on the other.

For 3≤n≤10 enumerate all rectangles with a+b=n and all nonincreasing row lengths within each one. The numbers of shapes with more edges than the formula are 0,0,0,0,0,1,32,149. Each is excluded by the following integer certificate, reconstructed by the [standalone verifier](verify-root-ade-cap-occupancies.js). Choose the first j rows and k columns with jk≥2(j+k). The code finds a flow on the available edges with degrees k on all j selected rows and j on all k selected columns, giving S²/Σdᵥ²=jk/(j+k)≥2. It checks a full flow by successive augmenting paths with integer capacities. Every excessive shape gets such a certificate.

For n≥11 some vertex has degree at most two. Otherwise both shores contain at least three vertices. If one shore has three vertices then every vertex on the other shore sees all three, giving K₃,₆. If both have at least four, the first three rows are full because the last column has degree ≥3; the fourth row has at least three entries. The first four rows and columns therefore have a matching of size four. Both alternatives contradict the previous necessary conditions. Delete a degree-at-most-two vertex; the sum of squared coordinates can only decrease, and the bound proof applies without a sum-zero assumption to the restricted differences (or recenter them). By induction from n=10 the count is at most 2n−4.

For attainment choose two coordinate blocks of sizes a,b with a+b≤n. Give them values b/(a+b) and −a/(a+b), all other coordinates zero. The squared norm is ab/(a+b). If this is <2, rescale to squared norm two: all ab cross-block pairs are then strict. Choose 1 and n−1, or 2 and n−2, or 3 and min(n−3,5) when both sizes are nonzero. These witnesses achieve the stated maximum.

For the lower endpoint, when n≥8 a balanced split of the coordinates gives the centered indicator of a set of size ⌊n/2⌋, of squared norm ⌊n²/4⌋/n≥2 and spread one. Scaling down gives no strict difference. For 3≤n≤7 suppose at most one root is blocked; permit that single ordered difference to exceed one. The resulting polytope in the sum-zero hyperplane is bounded, since the missing difference is ≤2 via a third coordinate. At any vertex the tight differences connect all n coordinates: otherwise shift two components against each other, keeping the mean zero and preserving all inactive constraints for small movements. Hence coordinate differences at a vertex are integral. With spread at most one its squared norm is ≤⌊n²/4⌋/n<2 (the centered cube), whereas spread two forces a unique maximum and minimum, all other coordinates at their midpoint, giving the original root eᵢ−eⱼ. Strict convexity leaves only these root vertices on the radius-√2 sphere. Finally center the vector (1,−1,−1,0,…,0) by subtracting its mean, then normalize to squared norm two. Its original squared norm is 3−1/n, so exactly the two gaps of size two become strict. This gives the minimum two.

## E: short dual certificates for the obstruction, no spherical grid

Work in the closed fundamental chamber of Eₙ with simple products wᵢ=αᵢ·x≥0, simple Gram G, and positive roots r in simple coefficient coordinates. The energy is wᵀG⁻¹w=2 and r is a blocker if r·w>1. A blocker set is upward closed in componentwise root order. Any larger ideal contains an upward subideal of the target size by deleting minimal members.

For the **upper** endpoint, enumerate all upward ideals C with size 17 in E6, 28 in E7, 30 in E8, respectively 25, 51, 24 ideals. For a putative strict realization, keep the inequalities Aw≥b consisting of chamber nonnegativity (b=0) and r·w≥1 for the minimal members of C (b=1). A dual vector c≥0 with cᵀb>0 and
```
(cᵀb)² ≥ 2 cᵀ A G Aᵀ c
```
rules out that strict realization: scale w slightly toward zero while preserving the finitely many strict blocker inequalities. The scaled norm is less than two, impossible by Cauchy–Schwarz applied to cᵀAw. The checker first proposes nonnegative rational weights and checks the displayed inequality exactly, using integers. For the remaining eight E8 cases it finds an independent active subset J and solves (AⱼGAⱼᵀ)c=bⱼ by exact determinants, requiring c≥0 and bⱼᵀc≥2. All 100 ideals are excluded.

Sharp directions w in the node order of the checker (a chain 0,…,n−2 and the last node attached at node 2) are e₀ for E6 and e₅ for each of E7,E8. Normalizing to squared norm two, the verifier counts exactly 16,27,29 strict products by squared integer comparisons. No numerical tolerance is used to accept any exclusion or attainment.
