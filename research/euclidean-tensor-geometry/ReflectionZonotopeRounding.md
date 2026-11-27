# Sharp Euclidean rounding constants for all finite real reflection systems

Normalize every mirror normal to squared norm two. Given any finite list r₁,…,rₘ of these vectors (repetitions allowed), and any cᵢ∈[−1,1], find signs εᵢ. There are two sharp uniform squared-error constants:

* **One signing:** minimize ‖Σ(εᵢ−cᵢ)rᵢ‖².
* **Unbiased rounding:** among distributions on signings with Eεᵢ=cᵢ for every i, minimize E‖Σ(εᵢ−cᵢ)rᵢ‖².

In both cases take the supremum over lists and coefficients. **The two constants are equal.** Their common value for each irreducible type is:

|Mirror system|Sharp squared error|
|:--|--:|
|Aₙ₋₁, n≥2|4⌊n²/4⌋/n|
|Dₙ, n≥4|4⌊n/2⌋|
|E₆, E₇, E₈|8, 14, 16|
|Bₙ/Cₙ|2n|
|F₄, H₃, H₄|8, 6, 8|
|I₂(m), even m|4|
|I₂(m), odd m|4/(1+sin(π/(2m)))|

For an orthogonal product sum the constants. These are hereditary errors for signing the *given list*, not covering radii allowing an arbitrary lattice translate. We give marginal-preserving upper bounds and deterministic lower examples, so both claims follow at once. Programming is required only for a small E₆ incidence decomposition; the [standalone exact verifier](verify-reflection-zonotope-rounding.js) checks it.

## Reduction to independent vectors and sums of block costs

Fix c and z=Σcᵢrᵢ. The fiber of the coefficient cube mapping to z is a compact polytope. Express c as a distribution on its vertices with that mean. At each vertex the fractionally weighted vectors are independent: otherwise a nonzero dependency would allow a small motion in both directions inside the fiber. All other signs are fixed. Round the independents preserving their means and mix over the fibers' vertices. The center z is unchanged throughout. Thus it suffices to round independent lists; a shorter list can be extended to a full root basis by adjoining fixed signs. Single independent random roundings cost at most two per vector. More generally, partition a basis into blocks and round the blocks **independently** with their correct means: errors have mean zero, so expected squared errors add even when the spans are not orthogonal.

In particular the always-valid bound in rank d is 2d. A full orthogonal root frame attains it at c=0. Types B/C and F₄ contain coordinate frames; H₃ and H₄ also contain the coordinate axes in their usual real models (see the [explicit reflection models](ReflectionCapOccupancies.md)). In E₈ use the eight roots e₁±e₂,e₃±e₄,e₅±e₆,e₇±e₈; the seven orthogonal to e₇+e₈ form a frame in E₇. Even dihedral systems have two perpendicular axes.

## An incidence block of type A

Write rᵢ=eᵤ−eᵥ in n coordinates; their column matrix B is a directed incidence matrix. Set t=(1+c)/2, b=Bt, and round t to binary x subject to
```
0 ≤ x ≤ 1,  floor(b) ≤ Bx ≤ ceil(b).
```
This polytope contains t and is integral: every square incidence submatrix has determinant 0 or ±1 by expanding a column with at most one nonzero, or, if none exists, summing its rows; adjoining signs and unit rows preserves total unimodularity. Distribute x over integral vertices with mean t. With fⱼ the fractional part of bⱼ, each component of Bx has variance fⱼ(1−fⱼ). The zero column sums imply Σfⱼ=q is an integer. Consequently
```
E‖2B(x−t)‖² = 4Σ fⱼ(1−fⱼ) ≤ 4q(n−q)/n ≤ 4⌊n²/4⌋/n.
```
For the reverse inequality take path columns eᵢ−eᵢ₊₁, q=⌊n/2⌋ and tᵢ the fractional part of iq/n, i=1,…,n−1. Every component of Bt is q/n modulo one. For any binary x the coordinates of Bx−Bt sum to zero and are integers minus q/n. The nearest such zero-sum vector has q coordinates 1−q/n and n−q coordinates −q/n (equalize any two integers differing by two or more). This gives the very same lower bound for every signing.

This flow-rounding ingredient is classical; compare [Doerr on linear discrepancy of totally unimodular matrices](https://researchportal.ip-paris.fr/en/publications/lsubpsub-linear-discrepancy-of-totally-unimodular-matrices/). For general context on binary rounding versus arbitrary lattice covering see [Li and Nikolov](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ESA.2020.69). We do not assert novelty of the classical components.

## Odd D and exceptional E₆

For odd n, any independent n-tuple of Dₙ roots has integer coordinate determinant, hence square Gram determinant. Its graph of nonorthogonal pairs cannot have zero edges (Gram determinant 2ⁿ) or exactly one edge (Gram determinant 3·2ⁿ⁻²). With two disjoint edges, round their two A₂ blocks at cost 8/3 each. With two incident edges, their three independent roots generate an irreducible simply-laced rank-three subsystem, hence an A₃ block, of cost 4. In both cases round the remaining singletons independently to get at most 2(n−1). The n−1 orthogonal roots e₁±e₂,…,eₙ₋₂±eₙ₋₁ attain it. For even n the same construction is a full frame.

For E₆ the following finite lemma suffices: every independent six roots can be partitioned into A₂+A₂+A₂, A₃+A₃ or A₅+A₁ blocks. The plus signs here denote a partition, **not orthogonality** between its blocks. Each partition costs eight by the type A bound. To verify the lemma enumerate the 36 positive roots in simple coordinates and all 1,947,792 six-subsets of their axes; signs do not affect the tests. In order, look for a perfect matching of nonorthogonal pairs; two disjoint connected triples; or a five-subset of Gram determinant six. The last test identifies A₅ for an independent basis: closing its five roots under their reflections preserves their integral span, and among rank-five simply-laced root systems only A₅ has determinant six. Similarly connectivity of an independent triple identifies A₃. Finally, test that every uncategorized six-subset is singular. The branch counts (including dependent sets that pass an early test) are:

|First test that accepts|Six-subsets|
|:--|--:|
|Three pairs|1,781,514|
|Two connected triples|62,220|
|Five-subset of determinant 6|46,656|
|Remaining, singular|57,402|

The four mutually orthogonal E₆ roots with simple coordinates (1,0,0,0,0,0), (0,0,1,0,0,0), (0,0,0,0,1,0), (1,2,3,2,1,2) show eight cannot be lowered.

## Odd dihedral types

An independent pair of axes can be oriented at angle 0<θ≤π/2. For this pair the signing parallelogram is, up to translation, 0, 2r, 2s, 2r+2s. Triangulate along the shorter diagonal joining 2r and 2s. Each triangle has squared circumradius 4/(1+cos θ). Barycentrically rounding any point z in a triangle to its three vertices preserves both coefficient means; its mean squared error is the squared circumradius minus the squared distance from z to its circumcenter. Conversely the first triangle's circumcenter is in the triangle and the fourth vertex is no closer (its excess squared distance is 8r·s≥0). Thus the pair's worst deterministic and unbiased errors both equal that radius. Maximize θ among mirror axes: for odd m the largest acute angle is π/2−π/(2m), giving the displayed value.

## Consequence for six-dimensional kissing transversals

For any translated E₆ root zonotope K with generating segments [−rᵢ,rᵢ], let its signed sums mean *all* endpoint choices (not only extreme vertices). If every signed sum has squared norm at least L, then every z∈K has squared norm at least L−8: the signing with mean z above has E‖S‖²=‖z‖²+E‖S−z‖². For example, in the [73-point complete-E₆-axis branch](KissingE6BiasedTransversals.md), L=48 implies squared distance at least 40 and hence a common unit direction with projection ≥√40 for every transversal sum. This does not settle the unrestricted kissing number.
