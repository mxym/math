# Eight common axes force D5, and twelve missing equatorial roots still suffice

This extends the [ten-axis A₄ rotation and ten-omission theorem](KissingE6A4SpinTen.md). All roots and kissing points have squared norm two.

**Mixed systems:** If a six-dimensional kissing configuration has a representative of each axis of two distinct E₆ systems, and they share at least **eight** axes, their common signed roots form D₅ (20 axes).

**Partial section:** A six-dimensional kissing configuration containing two complete 16-point D₅ spin layers at heights ±√3/2 and **at least 28 of the 40** signed equatorial D₅ roots has at most 72 points. This does not presume that all 20 equatorial axes are represented, or restrict the other points to the equator.

It follows that in the hypothetical 73-point complete-E₆-axis branch the strict blocker test and two-disjoint-negative-edges test both hold already at **p≥8** true antipodal pairs. This does not rule out p=8 or solve the kissing problem.

## The small intersections

At least ten common axes are covered by the earlier theorem. For eight or nine, their common roots form a simply-laced root system of rank at most six. Any subsystem containing A₄ is covered by the earlier rotation atlas; containing D₄ already gives 12 axes. The remaining types are:
```
A₃+3A₁ (rank 6, determinant 32);
2A₂+2A₁ (rank 6, determinant 36);
A₃+2A₁ (rank 5, determinant 16);
3A₂ (rank 6, determinant 27);
A₃+A₂ (rank 5, determinant 12).
```
The first two full-rank determinants are not three times a square, so they cannot embed as full-rank root sublattices of E₆.

Take the normal to any five-dimensional subspace spanned by roots and move it to a dominant E₆ chamber. Exactly five simple products then vanish: the perpendicular positive roots are supported on those vanishing coordinates and must span rank five. Thus the full perpendicular root system is obtained by deleting one Dynkin node. Its possible types and determinants are D₅ (4), A₄+A₁ (10), 2A₂+A₁ (18), A₅ (6). For A₃+A₂ none divides 12 with quotient an integer square. For K=A₃+2A₁ only D₅ works and the lattice extension has index two. It is unique inside its given Euclidean span. Indeed all even index-two extensions are formed by adjoining an order-two class in K*/K of squared norm 0 modulo 2. In A₃ the only such order-two candidate before the norm condition is the half-partition weight (1/2,1/2,−1/2,−1/2), of norm squared one: the A₃ dual consists of sum-zero coordinates with all differences integral and its quotient by A₃ is cyclic of order four. In each A₁ the nonzero class has squared norm 1/2. The **only** nonzero two-torsion combination of even norm is the sum of all three classes. Consequently the two D₅ lattices in this hyperplane coincide, as do all their norm-two roots.

For the remaining 3A₂ case, in each orthogonal A₂ factor let pᵢ=eᵢ−(1/3)1, i=1,2,3. Outside roots project to either zero or ±pᵢ in each factor, because their coordinate differences are integers of magnitude at most one. Norm two requires one nonzero projection in every factor. The independent permutations in the three Weyl groups force all 27 choices of indices for any one choice of the three signs, together with their negatives. These are exactly the 54 remaining roots. Thus an extension amounts to choosing one three-sign pattern modulo simultaneous reversal.

Two inequivalent choices differ in exactly one factor after choosing the global signs. Write their reference roots as (pᵢ,pⱼ,pₖ) and (−pₐ,p_b,p_c). Their product is
```
−[i=a]+[j=b]+[k=c]−1/3.
```
For i=a and j≠b, k≠c this is −4/3, so any compatible sign selection must agree across the two representatives. For each fixed i the corresponding bipartite graph is connected: any two pairs (j,k) have a common neighbor avoiding both entries coordinatewise. Hence all signs at fixed i in either system equal one value sᵢ. For i≠a and j=b, k=c the product is 5/3, so sᵢ=−sₐ for all i≠a. Three binary signs cannot do this. This excludes the last case.

## Up to twelve equatorial omissions

Keep the setup and proved chamber lemmas of the [ten-omission proof](KissingE6A4SpinTen.md), which do not depend on the number of omissions. In particular every extra is either centered (a unique largest signed horizontal coordinate, exceeding one or of exceptional shape (1,1/2,1/2,1/2,1/2) in absolute values) or has all ten positive coordinate-pair sums strictly exceeding one in its signed orthant, with largest absolute coordinate at most one. A centered group requires 4+k missing incident signed roots and has at most k+2 points for k≤3, or eight for k=4.

Let m≤12 be the actual number of omissions. If all extras are centered, their number of distinct centers r satisfies 4r≤2m, hence r≤6. With r≤5 and all k≤3 the old count Σ(k+2)≤m+binom(r,2)−2r≤m still works. If r=6 then m=12 and all k=0, so there are at most twelve points. If a center has k=4, three centers would require at least 8+4+4−3=13 omissions; any second center with k′ free slots requires m≥8+4+k′−1. Thus this case also contributes at most m points.

Otherwise fix a noncentered point and change coordinate signs so its ten required omissions M₀ are exactly the pair sums eᵢ+eⱼ. Write e=m−10∈{0,1,2} for the extra omissions. Every other noncentered point has the same signs: changing any nonempty set of coordinate signs changes at least four of the ten signed pair sums. No negative signed center is possible, since such a center would need four incident roots outside M₀.

Call a positive center i affected if some omitted extra difference is eᵢ−eⱼ. At an unaffected center all satellites are positive: otherwise its root eᵢ−eⱼ would strictly block the point (a zero satellite at a>1 blocks both choices, and an exceptional satellite is nonzero). Moreover all constraints eᵢ−eⱼ for this largest coordinate are retained, so the horizontal range is at most one. Noncentered points are likewise positive with range at most one. The second chamber certificate of the ten-omission proof applies to every one of these points: their horizontal coordinate sum exceeds 9/4. They project with length greater than one onto the same signed all-ones unit direction; subtracting these projections leaves pairwise strictly negative products in dimension five. Hence there are at most six points in this entire unaffected group, noncentered points included.

There are at most e affected centers. Each of their free slots consumes a different extra directed difference eᵢ−eⱼ, so Σk≤e among them, and k≤2. Their total is at most 2e+e. Combining the groups gives at most 6+3e≤10+e=m extra points. With the retained roots and both layers the total is at most (40−m)+32+m=72.

The [short exact checker](verify-kissing-e6-eight-axis-expansion.js) independently lists the ADE cases, performs the 3A₂ sign propagation, checks the order-two glue parity and verifies the finite integer counting inequalities. The only continuous chamber checks used are the already verified two eight-facet polytopes.

Finally, the standard projective equality argument in the ten-axis proof now gives the claimed strict expansion: equality would supply a distinct jointly represented E₆ with all p≥8 antipodal axes in the intersection. The mixed theorem forces D₅; at least 20+p≥28 of its signed roots occur, and the two off-section E₆ halves force both full parity layers. The partial-section theorem contradicts 73. The two-edge matching follows by the same single-vertex-deletion argument as before.
