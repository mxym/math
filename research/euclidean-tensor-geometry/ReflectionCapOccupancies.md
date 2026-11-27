# Exact open 60-degree cap counts for all irreducible finite real reflection systems

For a finite real reflection group in its essential representation, put **both unit normals to every distinct reflecting hyperplane** on the sphere. For a cap of angular radius 60° write b for the number of these points strictly inside it. The center is arbitrary on the same sphere. Together with the [ADE table](RootADECapOccupancies.md), the following gives the sharp maximum in every irreducible type, and the sharp minimum when the center itself is not a root direction. For non-simply-laced systems the normalization is essential: the counts are of directions, not of unnormalized length thresholds or repeated scalar multiples.

|remaining type|maximum|minimum at a nonroot center|
|:---|:---|:---|
|Bₙ or Cₙ, n=2,3,4,5,6|3, 6, 9, 12, 16 respectively|min(n,4)|
|Bₙ or Cₙ, 7≤n≤11|21|4 at n=7; 0 at n≥8|
|Bₙ or Cₙ, n≥12|2n−1|0|
|F₄|11|6|
|H₃|10|6|
|H₄|26|21|
|I₂(m), m≥3, including G₂=I₂(6)|ceil(2m/3)|floor(2m/3)|

Thus A, B/C, D, E, F, H and I₂ are all covered. This statement is about irreducible **real** reflection groups; it is not a classification of arbitrary sphere packings or caps of other angles. The [standalone verifier](verify-reflection-cap-occupancies.js) uses exact integer or quadratic-field comparisons for every acceptance.

## Dihedral directions and the B/C series

The 2m dihedral root directions are equally spaced by π/m. A 120° open arc covers 2m/3 spacings, so the ceiling is attained and the floor is attained at a nonroot center. When 3 divides m, an endpoint is a root direction exactly when the center is one too; every nonroot center then gives exactly 2m/3.

Scale the cap center to squared norm two and arrange its B/C coordinates a₁≥⋯≥aₙ≥0. Normalized Bₙ and Cₙ give identical directions: the Dₙ roots together with the signed axes. Hence the D count increases by h=#{i:aᵢ>1/√2}, which is at most three.

If a₁>1, [the D argument](RootDnCapMultiplicities.md) gives at most 2n−2 sum/difference blockers. Also h≤2. If h=2, equality in that D bound is impossible: in the notation of the D proof, equality requires either k=0 (all leaves smaller than a₁−1<1/2), or k=3 with a triangle on all three remaining leaves. In the latter case the one leaf above 1/√2 already uses more than 1/2 of squared norm, and the edge between the other two uses more than another 1/2. This contradicts the leaf squared norm <1. Thus the total is at most 2n−1; the axis direction √2e₁ attains this value.

When a₁≤1 only strict sum-edges can occur. Enumerate the isolated/universal threshold-graph strings from the D proof, now marking the h vertices with aᵢ>1/√2. One need only mark the first h in decreasing degree order: larger weights have larger neighborhoods outside the two vertices being compared, and vertices tied in degree are interchangeable by this nesting. A disjoint family of four blocked supports, allowing both edges and marked singletons, is impossible since each support costs strictly more than 1/2 of squared norm. A K₃,₆ of strict sum-edges is again impossible. Exhaust h=0,…,min(n,3) for 2≤n≤12. After those two tests, respectively 0,0,0,0,0,0,0,4,24,79,82 excessive strings/markings remain. For each of these 189 cases the verifier certifies nonnegative **integer** weights on its edges and marked vertices. If p is total edge weight, t total singleton weight, and dᵢ the weighted incidences, the exact test is
```
(p+t/√2)² ≥ 2 Σdᵢ² .
```
This is impossible by the strict blocker inequalities and Cauchy–Schwarz. Weight search is heuristic; every accepted certificate is verified by squaring with a sign check over the integers. For n≥13 the smallest coordinate is unmarked and has at most two strict sum-neighbors, since otherwise the top three yield a K₃,₆. Delete it and induct from n=12.

For attainability in ranks 2 through 6 normalize respectively (5,4), (1,1,1), (3,3,3,2), (16,16,16,8,8), (13,10,10,10,10,10). Seven equal nonzero coordinates give 21 in the next ranks, and the axis witness handles the large ranks. For n≥8 equal coordinates give zero blockers.

## Exact chamber certificates in the remaining small ranks

The B chamber is sorted nonnegative coordinates. For F₄ take the [standard roots](https://qseries.org/fgarvan/papers/f4.pdf): the D₄ roots, signed coordinate axes, and all signed half-vectors (±1,±1,±1,±1)/2. Work in the chamber a₁≥a₂+a₃+a₄, a₂≥a₃≥a₄≥0. For long roots r the test is r·a>1; for short roots it is r·a>1/√2. In either case normalize the linear form by its threshold. Nonnegative chamber-gap coordinates then define an order by coefficientwise dominance. Strict blockers are upward closed.

To prove a lower bound L, permit every upward ideal with L−1 members as an exceptional set and impose all remaining upper inequalities. It suffices to impose the maximal remaining forms. Intersect with the chamber and the harmless cap a₁≤3/2. Enumerate every vertex by exact nonsingular active bases. If all squared norms are at most two, strict convexity forces every norm-√2 point to be a norm-√2 vertex; a root vertex does not affect a nonroot minimum. The code checks all possible equalities. In B ranks 2,…,7 the respective ideal counts are 2,2,4,4,4,4. Witnesses for the minima in ranks 2 and 3 are normalized (15,5) and (17,9,4). In ranks 4 to 7 the vector (1,1/√2,1/√2,0,…,0) has exactly four strict blockers. In F₄ the four five-member ideals are all excluded; an explicit six-blocker center is
```
((1+√2)/2, 1/2, 1/2, (√2−1)/2).
```
The equality of some products to the threshold at these algebraic witnesses matters: sampling only rational directions can miss the minimum. For the F₄ upper bound, all 14 upward ideals of size twelve fail an exact dual test as in the ADE proof. More explicitly for inequalities Aa≥b, an independent active row subset J with c=(AⱼAⱼᵀ)⁻¹bⱼ≥0 and cᵀbⱼ≥2 rules out strict realization by rescaling and Cauchy–Schwarz. Normalizing (4,1,0,0) gives eleven. All F₄ comparisons are in Q(√2).

For H₃ and H₄ use the simple Gram matrix with diagonal 2, the initial chain edge −φ and all other chain edges −1, where φ=(1+√5)/2. Generate the 30 or 120 roots by simple reflections. In nonnegative simple-product coordinates w, enumerate upward ideals and use the same vertex/dual arguments, now with squared norm wᵀG⁻¹w and dual Gram AGAᵀ. The harmless coordinate caps are wᵢ≤2. For the H₃ minimum/maximum there are 3 exceptional ideals of size five and 4 forbidden ideals of size eleven; for H₄ there are 2 of size twenty and 6 of size twenty-seven. Every equality relevant to a minimum is checked directly against root directions. Integer pairs represent Q(φ) numerators with positive denominators; determinants, Cramer's rule and signs are exact. Directions in simple-product coordinates for the H₃ minimum/maximum are (3,2,1) and (0,0,1), for H₄ (0,1,0,2) and (1,0,0,0). The checker normalizes and counts these witnesses using squared comparisons.
