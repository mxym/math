# Mixed E6 intersections down to ten axes and the ten-omission D5 spin section

All vectors have squared norm two and distinct kissing points have inner product at most one. We prove:

1. Two **distinct** E₆ root systems whose axes are jointly represented, one sign per axis sufficing, cannot share ten or more axes unless their intersection is D₅ (20 axes).
2. In six dimensions, two complete 16-point parity spin layers over D₅ and at least 30 of its 40 signed equatorial roots imply at most **72** total points.
3. Consequently in any hypothetical 73-point configuration representing all 36 axes of a fixed E₆ and having p≥10 true antipodal pairs, every nonempty outsider set S with mutual products at least −1 has **at least |S|+1 distinct signed original blockers**.

These are conditional obstructions, not a new bound for the unrestricted six-dimensional kissing number.

## Exact orientation atlas about A₄

Embed A₄ as eᵢ−eⱼ in the sum-zero subspace on five coordinates; its perpendicular space is a plane. Put pᵢ=eᵢ−(1/5)1 and qᵢⱼ=pᵢ+pⱼ. Every other E₆ root projects horizontally to 0, ±pᵢ, or ±qᵢⱼ. Indeed all coordinate differences are integers of magnitude at most one. Nonzero projections have full horizontal permutation orbits of size 5 or 10 at each perpendicular vector. There are 52 roots outside A₄. The roots of zero projection form a simply-laced subsystem in a plane, of size 0, 2, 4, or 6, congruent to 52 modulo 5; hence exactly two, ±h.

The roots perpendicular to h form A₅: a root of E₆ has 30 perpendicular signed roots (check in simple coordinates via the [root generator](verify-kissing-e6-exact-blocker-spectrum.js), or use the standard E₆ root stabilizer); only A₅ among rank-at-most-five simply-laced systems has 30 roots. Thus beyond A₄, ten roots are perpendicular to h. In the perpendicular plane use h as the vertical direction; write z for the coordinate normal to A₄+ℝh. A root outside that span gives a rank-six extension lattice of determinant 10z²=3I², I a positive integer. Together with z²≤2, the only positive options are 3/10 and 6/5. For the projections ±pᵢ (squared norm 4/5) and ±qᵢⱼ (squared norm 6/5), the h-direction component is 0 or ±1/√2 by integrality. This also excludes z=0 for both nonzero projection types. Thus the p roots have z²=6/5 and zero component along h, and the q roots have z²=3/10 and h-component ±1/√2.

Choose the normal z-direction so that the five pᵢ at the positive z-level occur (permutation symmetry and the ten-root count). Integrality of products with these roots fixes the z-sign of every qᵢⱼ: pₗ·qᵢⱼ is an integer minus 2/5 and the transverse contribution must be −3/5 rather than +3/5. Counting the remaining forty roots forces both h signs for all qᵢⱼ. Thus the 26 axes outside A₄ have these reference representatives, recording plane coordinates as (a√(3/10), b/√2):

|horizontal|a|b|axes|
|:--|--:|--:|--:|
|pᵢ|2|0|5|
|qᵢⱼ|−1|±1|20|
|0|0|2|1|

Conversely the displayed description is forced up to an orthogonal map of the plane for any E₆ containing A₄. The model is invariant under reflection in the first plane axis. Relative placements of a second system are therefore parametrized by a rotation of angle θ∈[0,π], up to reflection.

For a pair of reference roots, one from each system, let C=10 times their horizontal product, D=3aa′+5bb′, E=ba′−ab′. With y=√15 tan(θ/2), ten times the full product equals
```
C + D(15−y²)/(15+y²) + 30Ey/(15+y²).
```
If the absolute product is ≤1 there is no sign restriction. If it lies strictly between 1 and 2 then the product of selected signs must be opposite to its sign. At absolute product 2 the axes coincide; select the same actual representative in both copies instead, so the required sign-product equals the sign of the reference product. This common-representative restriction loses nothing. The shared A₄ imposes no extra restrictions since it belongs to each individual root system.

The resulting graph of sign equalities or oppositions is consistent exactly when signs can be propagated around every cycle. The [exact verifier](verify-kissing-e6-a4-spin-ten.js) solves this graph at every possible angular change: all roots y≥0 of the four threshold polynomials at tenfold products −20,−10,10,20 are isolated exactly, including the coincident-axis exceptions. There are 12 finite endpoints. The verifier compares rational numbers and quadratic surds using only integer signs and squares; its rational interior tests are 1, 2, 9/4, 5/2, 31/10, 4, 6, 7, 9, 12, 20 and 40. Every open interval fails. Among endpoints, only y=0 (equal systems) and y=5 (20 common axes) pass. At y=∞ the systems share 11 axes and fail. In particular a jointly represented distinct pair containing A₄ has exactly 20 common axes and hence D₅ by the [≥12-axes theorem](KissingE6MixedIntersections.md).

For 10 or 11 common axes, if their intersection contains neither A₄ nor D₄, the ADE list in rank at most six has only A₃+A₂+A₁ in this range (10 axes). Its lattice determinant is 24, not three times an integer square, so it cannot have full rank in E₆. A D₄ already supplies 12 axes. This proves assertion 1.

## Counting through ten missing signed D₅ roots

The equatorial D₅ roots are ±eᵢ±eⱼ in five horizontal coordinates. A full parity layer consists of all 16 sign vectors of one parity, divided by two, at one height ±√3/2; the two layer parities can be chosen independently. Let m≤10 be the number of actually missing signed equatorial roots. For an extra point (v,z) outside all these roots and layers write a≥b≥c≥d≥e≥0 for its sorted absolute horizontal coordinates. Maximizing over the parity at the height on the same side as z gives
```
L=a+b+c+d−e,   L+√3|z|≤2,
2≤F=a²+b²+c²+d²+e²+(2−L)²/3.
```
First consider sorted coordinates with a≤1, d+e≤1 and L≤2. The checker solves all five-row active bases of the eight inequalities (four order comparisons, e≥0, and these three bounds). Its only vertices with F≥2 are (1,1,0,0,0) and (1,1/2,1/2,1/2,1/2), both at equality. Strict convexity of F excludes any nonvertex. The first is an equatorial root; the second has z=0. Thus an extra is **centered** (a>1, or the second exceptional vector), unless a≤1 and d+e>1. For a>1 the largest coordinate is unique because a+b≤L≤2.

For an occupied signed center coordinate i, a point strictly blocks at least one signed incident root on every other coordinate slot j: take the sign matching vⱼ. A zero satellite can occur only for a>1 and then both signs are blocked. Let k≤4 be the number of slots with both incident signs missing, giving 4+k required missing incidences. When k≤3, the other slots have fixed nonzero signs for every point at this center. Omitting the center (whose pair product is ≥1) and these fixed slots leaves pairwise **strictly negative** products in dimension k+1, the k free slots and height. Such a set has at most k+2 vectors by strict obtuseness (an affine dependence forces equal oppositely supported convex combinations with negative mutual product).

If k=4, at most eight centered points are possible. If all are exceptional, the four tail signs have Hamming distances at least two, so pair up strings across one bit. Otherwise take a point with a>1; its residual after deleting the center has strictly negative product with every other residual, which are mutually nonpositive. A zero residual allows no other point. For a nonzero one project the others to its four-dimensional perpendicular space. Each subtracted product is positive, leaving strict obtuseness, hence at most five others. A k=4 center consumes eight missing signs and no second center can coexist for m≤10, since it requires four and can share at most one.

Suppose first all extras are centered and no k=4 occurs. For r centers, 4r≤2m since each missing root is incident with at most two centers. Thus r≤5. Two distinct centers share at most one signed incident root, including opposite signs of the same coordinate. The total number of extra points is bounded by
```
Σ(kᵢ+2) = Σ(4+kᵢ)−2r ≤ m + binom(r,2)−2r ≤ m.
```

Finally, if an exceptional-to-this-count point has a≤1 and d+e>1, all ten horizontal pair sums strictly exceed one. Therefore m=10 and the omissions are **exactly** the ten pair sums in its signed orthant. Every centered extra also lies in this same positive orthant after sign changes: each slot has just one eligible missing sign on its support, fixing both signs. Every other noncentered extra does likewise. Both orientations of every coordinate difference are retained, so a−e≤1. We claim every extra has a+b+c+d+e>9/4. Otherwise use the eight-row polytope formed from the same order/nonnegativity, L≤2, a−e≤1 and 4(a+b+c+d+e)≤9. The only vertex with F≥2 is (1,1,0,0,0), at equality, and strict convexity again gives no nonroot. This second eight-row computation is included in the verifier. Projection of each extra on the common unit vector (1,1,1,1,1,0)/√5 thus exceeds one. After subtracting that projection, mutual products are strictly negative in dimension five, so there are at most six extras. In all cases there are at most m, yielding (40−m)+32+m=72. This proves assertion 2.

## Strict expansion

For nonempty projectively compatible outsiders S, the outsider lines together with the original axes they do not block form a projective code of size |S|+36−|B(S)|. All original axes are represented, so the signed blockers contain at most one root per axis. By [Anstreicher's projective E₆ theorem](https://optimization-online.org/2001/01/248/) the count is at most 36 and equality gives another E₆. The systems would be distinct and jointly represented, with all p paired axes common. By assertion 1 their intersection is D₅ and at least 20+p≥30 of its signed roots occur. As detailed in the [two-layer argument](KissingE6D5EightOmissions.md), jointly representing the 16 non-D₅ axes of each system forces a complete parity class of 16 at each height, contradicting assertion 2. Thus |B(S)|≥|S|+1. The same argument as the [earlier negative-edge matching proof](KissingE6MixedIntersections.md) now also forces two vertex-disjoint negative edges in the outsider graph when p≥10.
