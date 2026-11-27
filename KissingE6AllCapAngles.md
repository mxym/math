# Spherical cap discrepancy and all angular occupancy thresholds for E6

Let Φ be the 72 E₆ roots of squared norm two, let ‖x‖²=2, and count r∈Φ with x·r>h (open cap) or x·r≥h (closed cap). The two short tables below determine the **sharp largest and smallest counts for every threshold**, including when root centers x∈Φ are disallowed. A cap of angular radius θ corresponds to h=2 cos θ. The normalized spherical cap discrepancy is **exactly 5/18**, attained by exactly 27 unoriented D₅ equators. No kissing-configuration extension is assumed.

## Reading the tables

For h>0 put t=2/h². A_k and B_k below are squared norms.

* **Maximum open count:** the largest k with A_k<t. For closed caps replace < by ≤.
* **Minimum open count:** the least k with B_k≥t. For closed caps replace ≥ by >.
* **Nonroot centers:** at equality in the closed maximum test ignore k=1 and k=17,…,21. At equality in the open minimum test ignore k=1,…,4. No other positive-threshold changes apply.

|k|A_k|k|A_k|
|:--|--:|:--|--:|
|0|0|17–21|2|
|1|1/2|22–25|10/3|
|2|2/3|26|16/3|
|3|3/4|27–29|6|
|4|4/5|30|10|
|5|5/6|31|34/3|
|6–8|1|32|46/3|
|9–11|5/4|33|18|
|12–16|4/3|34|30|
|||35|42|
|||36|78|

|k|0|1–4|5–7|8–10|11–12|13–14|15|16–36|
|:--|--:|--:|--:|--:|--:|--:|--:|--:|
|B_k|4/3|2|10/3|4|6|22/3|8|∞|

For h=0 the open hemisphere ranges from 16 to 36 and the closed hemisphere from 36 to 56 (endpoints attainable by nonroots). For h<0 use antipodality: the open count is 72 minus the closed count at −h, and conversely. The endpoints here are sharp; no assertion that every intermediate integer occurs is required.

For example, at h=1 an open cap ranges from 1 to 16 with unrestricted centers, and from 5 to 16 with nonroot centers. A closed cap ranges from 5 to 21, but its maximum decreases to 16 if the center is not a root. The strict/boundary distinctions matter.

## Proof by chamber optimization

Move x to the dominant chamber. Use simple inner products wᵢ=αᵢ·(x/h)≥0, so wᵀG⁻¹w=t for the simple Gram matrix G and a positive root with coefficient vector r has scaled product rᵀw. Positive-threshold sets are upward ideals in the positive-root order. Any upward ideal can be grown or shrunk by one root at a time. Enumerate all 833 ideals, starting empty and repeatedly adjoining a maximal remaining root, with diagram reversal allowed when taking extrema.

For every ideal C of size k compute the following two numbers:

1. **Forcing at least C:** impose w≥0 and rᵀw≥1 for its minimal roots. Minimize wᵀG⁻¹w. This convex quadratic program has a unique minimizer when C is nonempty. The verifier exhibits a set J of at most six active rows of Aw≥b. Set K=AⱼGAⱼᵀ, c=K⁻¹bⱼ. It checks c≥0, the proposed w=GAⱼᵀc satisfies *all* inequalities, and Aⱼw=bⱼ. This proves optimality directly by the supporting first-order inequality or Cauchy–Schwarz. Take the least objective value over ideals of size k to obtain A_k.
2. **Allowing at most C:** impose w≥0 and rᵀw≤1 for the maximal roots outside C; do **not** impose any lower bound on roots inside C. Maximize wᵀG⁻¹w. The polytope is unbounded precisely when some coordinate occurs in no upper row. Otherwise it is compact, and strict convexity means only a vertex can attain its maximum. Solve every independent six-row active basis exactly, retain feasible vertices, and take the greatest squared norm. Maximizing this over all C of size k gives B_k.

Scaling explains all four tests. To obtain strict lower inequalities at norm t one must exceed the minimum, and conversely scaling a minimizer up gives strict lower inequalities. To obtain strict upper inequalities one must stay below the maximum, and conversely scaling down from a larger norm makes the inequalities strict. In nonboundary cases the desired inequalities survive a small perturbation to a nonroot direction; for a weak minimum test with t<B_k one may first scale down to obtain the strict upper inequalities. For the closed maximum test with t>A_k the scaled witness has strict lower inequalities as well. At a finite equality, test whether any extremizing direction is a nonroot. In the closed dominant chamber the only root ray is that of the highest root, with simple products proportional to (0,0,0,0,0,1). The verifier checks the ray for every minimizing witness and every maximizing vertex. With B_k=∞, arbitrary sufficiently large nonroot norms are possible because the polytope has interior and an unbounded coordinate ray. For the h=0 minimum, any nonzero chamber vector has a positive coordinate i, hence all positive roots with coefficient i nonzero give strictly positive product. Taking a simple-product coordinate ray achieves the smallest such count, 16, at a nonroot. Generic chamber directions give 36.

The [standalone exact verifier](verify-kissing-e6-all-cap-angles.js) uses integer determinants, divisibility checks and rational comparisons throughout. The [sixty-degree blocker census](KissingE6ExactBlockerSpectrum.md) separately distinguishes the 33 individual mask orbits at that threshold; the tables here give extremal *counts* at every angle, not full mask classifications at other angles.

## Exact spherical cap discrepancy

Use the [usual supremum discrepancy](https://www.sciencedirect.com/science/article/pii/S0885064X02000067), the absolute difference between the point fraction in a cap and its normalized surface measure. By taking complements it is enough to bound both deviations for caps of radius at most a hemisphere, allowing either boundary convention. For c=h/2∈[0,1] their measure on the unit S⁵ is
```
F(c) = 1/2 − (8/(3π)) ∫₀ᶜ (1−s²)^(3/2) ds.
```
Write k for the point count. For the excess k/72−F, counts k≤20 are harmless. Otherwise c≤1/√(2A_k) and F(c)≥1/2−8c/9 since π>3. For each k=21,…,36 the table gives 4096≤2A_k(56−k)², proving the excess is at most 20/72.

For the deficit F−k/72, if k≥16 simply use F≤1/2. When 3≤k≤15, the B table gives c≥1/4; when k≤2 it gives c≥1/2. The decreasing integrand and π<22/7 give
```
F(u) ≤ 1/2 − (28/33)u(1−u²)².
```
At u=1/4 this is strictly below 23/72, and at u=1/2 it is strictly below 20/72, as required. These bounds cover positive thresholds; a degenerate cap of zero area can contribute at most one point.

At the hemisphere the open count 16 attains the deficit 20/72=5/18 and the closed count 56 the same excess. The positive-threshold estimates are strict for equality purposes (in the excess argument F>0 when k=20, and 8/(3π)<8/9 when c>0). The dominant minimum-hemisphere normals have simple products supported only at node 0 or only at node 4. Indeed these are the only coordinates occurring in just 16 positive roots, and their support lists differ, as witnessed by the two simple roots. Their perpendicular root systems are the D₅ diagrams obtained by deleting the corresponding terminal node. The Weyl orbits of the two unit normals together have 54 elements, checked by applying the simple reflections in simple-product coordinates. Pairing each with its negative leaves precisely 27 equators. All these centers are nonroots.

## A multiple-outsider constraint

If q distinct kissing points xⱼ all strictly block the same m E₆ roots (xⱼ·r>1), let z=q⁻¹Σxⱼ. Then ‖z‖²≤1+1/q and r·z>1 for every common blocker. Since the lower inequalities are strict, one can shrink z a little and still keep them weak, so A_m<1+1/q. In particular three outsiders can have at most **11** common blockers and four or more can have at most **8**. This necessary condition alone is not claimed sharp, nor does it settle the six-dimensional kissing number.
