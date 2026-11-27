# The spherical cap discrepancy of every irreducible finite real mirror system

For a finite irreducible real reflection group take the two **unit** normals to every distinct mirror, each once. How far can their fraction in a spherical cap deviate from the surface area of that cap?

**Theorem.** In rank at least three the worst caps are exactly the hemispheres whose equator contains the largest number of normals. Thus
```
discrepancy = (largest number of equatorial normals) / (2 × number of normals).
```
This is a statement about *every aperture and every center*, not a restriction to hemispheres in the definition. Both open and closed conventions give the same supremum. The table lists unoriented maximizing equators. Long and short roots are normalized separately; this is not a radius-weighted or multiplicity-weighted root sample.

| Type | Number N of points | Discrepancy | Maximizing equators (rank ≥ 3) |
|:--|--:|:--|:--|
| A₁ | 2 | 0 | uniform on S⁰ |
| I₂(m), m≥3 | 2m | 1/(2m) | regular polygon; other arcs can also maximize |
| A_d, d≥3 | d(d+1) | (d−1)/(2(d+1)) | d+1 copies of A_{d−1} |
| D₄ | 24 | 1/4 | 12 copies of A₃ |
| D_d, d≥5 | 2d(d−1) | (d−2)/(2d) | d coordinate D_{d−1} sections |
| B_d=C_d, d≥3 | 2d² | (d−1)²/(2d²) | d coordinate B_{d−1} sections |
| E₆ | 72 | 5/18 | 27 copies of D₅ |
| E₇ | 126 | 2/7 | 28 copies of E₆ |
| E₈ | 240 | 21/80 | 120 copies of E₇ |
| F₄ | 48 | 3/16 | 24 rank-three B sections |
| H₃ | 30 | 1/6 | 6 decagonal sections |
| H₄ | 120 | 1/8 | 60 copies of H₃ |

Here A₂, B₂ and G₂ are covered by the dihedral row. Different Coxeter diagrams or dual realizations producing the same directions give the same sample. No assertion of optimality among point configurations of cardinality N is made. [Heitsch–Henrion](https://www.wias-berlin.de/people/henrion/spher-cap-disc-online.pdf) give a general finite formula for arbitrary configurations; here the conclusions are the explicit values, maximizers, and formulas uniform in the classical ranks.

## Hemispheres

Write M for the smallest open hemisphere count. Antipodality gives the candidate discrepancy δ=1/2−M/N. For A_d use the unit differences (eᵢ−eⱼ)/√2 in the zero-sum subspace of d+1 coordinates. The equatorial roots of a unit center are the differences within its blocks of equal coordinates. The maximum block count arises only from sizes d and 1, giving M=d.

In D_d take the unit (±eᵢ±eⱼ)/√2. With z zero coordinates and positive absolute-value multiplicities t₁,t₂,…, the number of equatorial roots is 2z(z−1)+Σ tᵢ(tᵢ−1). For fixed z the maximum has a single nonzero block, and the resulting expression is a strictly convex quadratic in z. Its maximum is at 0 or d−1. For d>4 only d−1 wins; for d=4 the all-equal-absolute center ties. This gives M=2(d−1) and in rank four the 4 coordinate plus 8 signed equal-absolute axes. The cross-polytope X_d={±eᵢ} has M=1 with precisely the coordinate axes as minimizing hemisphere normals.

## The infinite families: why a smaller cap cannot do worse

Let d≥3, x be a unit center, c>0 the cosine of the cap radius, and k the count. Complementation reduces everything to c≥0. Its area is
```
F_d(c) = 1/2 − C_d ∫₀ᶜ (1−s²)^((d−3)/2) ds,
C_d = Γ(d/2)/(√π Γ((d−1)/2)).
```
Log-convexity of Γ at successive half-integers gives √((d−2)/(2π))<C_d<√((d−1)/(2π)). Put h=M/N. We first treat A_d, d≥7, and D_d, d≥8. Here h=1/(d+1) and 1/d respectively.

**Excess of points.** The normalized A and D systems have mean square projection 1/d in every unit direction: the frame operator is scalar by irreducibility (or a coordinate calculation), with trace one after dividing by N. Hence k/N≤1/(2dc²), pairing each point with its antipode. For c≥c*=1/√(d(1−2h)) this gives k/N≤δ, strictly below δ after subtracting F_d(c), except for zero-area caps which contain at most one point. For c≤c* it suffices to have F_d(c*)>h since k/N≤1/2. In dimensions d≥16, the upper bound on C_d gives
```
F_d(c*) > 1/2 − √(16/(14·6)) > 1/16 ≥ h .
```
Here we used π>3, h≤1/d, and monotonicity of d/(d−2). For A₇,…,A₁₅ and D₈,…,D₁₅ the finite rational checks at c* are described below.

**Deficit of points.** There is nothing to prove when k≥M, because F_d(c)<1/2. For A_d with k<d, the range of the coordinates of x is at most 2√2 c. Otherwise a pair i,j realizing a larger difference forces not only (i,j) into the cap but, for each intermediate index b, at least one of the disjoint pairs of directed differences (i,b),(b,j). This forces d roots. The variance of numbers in an interval of length R is at most R²/4; since x has zero mean and norm one, R≥2/√(d+1). Thus c≥c₀=1/√(2(d+1)).

For D_d, if k≤M−2 then the largest raw root product is at most 2√2 c. Indeed each raw root ±eᵢ±eⱼ is the sum of two raw roots in 2(d−2) pairwise-disjoint ways using the intermediate coordinates and either sign there. A larger product would force the original root and at least one root from each pair, or M−1 roots. Also max_{i<j}(|xᵢ|+|xⱼ|)≥2/√d: placing a bound 1 on the sum of the top two moduli gives squared norm at most max(1,d/4). To see the latter, if the second modulus is b≤1/2 then the squared norm is ≤(1−b)²+(d−1)b², a convex function. Thus c≥1/√(2d)>c₀.

On [0,c₀] the density factor without C_d is ≥1−(d−3)c₀²/2>3/4 by Bernoulli's inequality. For d≥7,
```
1/2 − F_d(c₀) > (3/4) √((d−2)/(4π(d+1))) > 1/7 ≥ h ,
```
where the middle inequality already follows from π<4. This proves the strict deficit bound even when k=0.

There remains D_d at k=M−1, requiring just 1/2−F_d(c)>1/N. Move x to the dominant chamber with raw simple roots of squared norm two. Every coordinate wᵢ=αᵢ·x must be ≤√2 c: otherwise all positive roots containing node i belong to the cap, and there are at least M (the count on the corresponding hemisphere ray). Thus 1≤√2 c‖ρ‖, where ρ is the sum of fundamental weights: their pairwise Gram entries are nonnegative, so their squared-norm quadratic is increasing in the nonnegative wᵢ. For D_d, ρ=(d−1,d−2,…,1,0) and ‖ρ‖²=d(d−1)(2d−1)/6. Since 1/(√2‖ρ‖)≤c₀, the density lower bound gives
```
1/2−F_d(c) ≥ (3/4) C_d/(√2‖ρ‖) > 1/[2d(d−1)].
```
The last inequality follows by squaring and using 27d(d−1)(d−2)>8π(2d−1).

**The B family.** First the discrepancy of X_d is (d−1)/(2d) for d≥3, attained only on coordinate hemispheres. For 1≤k≤d−1 both deviations are immediate from 0≤F_d(c)<1/2 and are strict for c>0 (at c=1 at most one point is counted). For k=0 one has c≥1/√d; for k=d, c≤1/√d. Both endpoints are harmless because
```
1/(2d) < F_d(1/√d) < 1/2−1/(2d).
```
The program checks d=3,…,15. For d≥16 the left bound follows from F_d(1/√d)>1/2−1/√(2π), and the right bound follows from the lower estimate at c₀ above (whose displayed 1/7 exceeds 1/(2d)). The B_d sample is the disjoint union of D_d and X_d. For d≥4 both attain their discrepancies on each coordinate hemisphere, with the same sign, so the weighted average of their discrepancies is attained there and nowhere else, giving (d−1)²/(2d²). B₃ is verified separately.

## Finite ranks and exact certificates

The [standalone verifier](verify-mirror-root-spherical-cap-discrepancy.js) covers the remaining classical ranks A₃–A₆, D₄–D₇ and B₃, plus F₄,H₃,H₄. The [E₆ tables](KissingE6AllCapAngles.md) and [E₇/E₈ tables](KissingE7E8AllCapAngles.md) give the same result for those types. The method below includes all centers, including chamber walls and roots on the cap boundary.

Normalize simple roots to length √2 with Gram matrix G given by the Coxeter diagram (edge m gives −2 cos(π/m)). Generate the roots by reflection. Their positive simple coordinates may lie in ℚ(√2) or ℚ(√5). For a chamber vector use simple-product coordinates w≥0 so the norm squared is wᵀG⁻¹w. Positive roots with product at least one form an upper ideal in coordinatewise ordering; this remains true without crystallographic integrality. Enumerate all such ideals (including ideals not realizable by a single hyperplane, which do no harm). For each size k let Aₖ be the least achievable norm squared forcing all roots of a k-ideal weakly above one; let Bₖ be the greatest achievable norm squared keeping every root outside some k-ideal weakly below one. Taking the least over all feasible KKT minima for the former and the greatest over all feasible vertex maxima for the latter gives exact values, with an uncovered coordinate making Bₖ infinite. Conic Carathéodory bounds the active basis for a minimum by d; a compact polytope attains a convex maximum at a vertex. The linked [E₇/E₈ note](KissingE7E8AllCapAngles.md) gives the scaling argument in full.

For each k/N>δ certify F_d(1/√(2Aₖ))>k/N−δ; for each k<M certify F_d(1/√(2Bₖ))<k/N+δ. These force both deviations to be strict away from hemispheres. The program bounds the decreasing density by outward-rounded left/right rectangle sums on an integer mesh of 2,048 bins, using squared comparisons of integers or real quadratic field elements and 333/106<π<355/113. The same routine certifies the finitely many scalar integrals in the large-rank proof. No sampled cap center or floating-point quadrature is used as proof.

For B₃,F₄,H₃,H₄ the lists of positive-root counts on the chamber rays are respectively (6,7,5), (15,20,20,15), (12,13,10), (54,56,54,45). Only the minimizing single rays yield equality, since any multiple support takes the union of different ray-support lists (the simple roots witness that they differ). Closing these rays under reflections gives respectively 6, 48, 12, 120 signed normals. Dividing by two yields the table. Finally, a regular 2m-gon counts every arc with error at most one point versus its length in units of the point spacing (floor/ceiling, including endpoint convention); a singleton closed arc attains one. In rank one the sample is exactly the surface measure of S⁰.

```sh
node verify-mirror-root-spherical-cap-discrepancy.js
```
