# How many root inequalities can be deleted without creating an extra polar vertex?

Let R consist of the two normals to every reflecting hyperplane of a finite real reflection group, all scaled to squared norm two, in their essential span. Put P₀={x:r·x≤1 for every r∈R} and P(M)={x:r·x≤1 for every r∈R∖M}. Define τ as the largest integer such that
`P(M)=conv(P₀ ∪ M) for every M⊆R with |M|≤τ.`
This is an exact identity of continuous polytopes, not a radius estimate. It says adding the deleted signed roots themselves already describes the whole enlarged polar. Classically the *intact* root polytope and its face structure are extensively studied; see [Cellini–Marietti](https://arxiv.org/abs/1207.3429) and their [work on intact polar root polytopes](https://arxiv.org/abs/1502.06377). No priority is asserted.

**Classification for every nonempty normalized finite real mirror system:**

| System | τ |
|---|---:|
| A₁ | 0 |
| Aₙ, n≥2 | 1 |
| Dₙ, n≥4 | 2 |
| E₆ | 3 |
| E₇ | 4 |
| E₈ | 6 |
| Every other irreducible system and every reducible system | 0 |

Each entry includes a failure at the very next deletion size. The proof uses a general vertex-deletion principle, not a case-by-case search over removed subsets. The [exact verifier](verify-root-polar-puncture-thresholds.js) checks the exceptional entries by two separate mathematical tests: one on *unpunctured faces* and one on *punctured chamber inequalities*.

## 1. A clipping principle

Let Q=conv(V) be a finite polytope with spherical vertices of squared norm 2, dot products ≤1 for distinct vertices, and dot product **equal to 1 on every edge**. For a vertex r define the cut r·x≤1, which contains every vertex other than r.

If every face of dimension at most k is a simplex, then deleting at most k vertices agrees exactly with making their simultaneous cuts:
`conv(V∖M) = Q ∩ {x : r·x≤1 for all r∈M}.`
Indeed let x be a vertex of the right-hand side and F the minimal face of Q containing x. It is in the relative interior of F. At most |M| active cuts are available, hence dim F≤|M|; otherwise a nonzero tangent direction preserves all active equations and sufficiently small perturbations both ways remain feasible. Thus F is a simplex. Any removed vertex r of F has dot 1 with all the other vertices of F, and its strictly positive barycentric weight at x would give r·x>1. So F has no removed vertices, and x lies in conv(V∖M). The reverse inclusion is immediate.

If Q has a regular d-dimensional cross-polytope face F, choose one vertex from each of its d opposite pairs and delete them. Write its vertices c±bᵢ. Their common norm gives c⊥bᵢ; its regular cross-polytope geometry makes the bᵢ orthogonal. Adjacent vertices have dot 1, so ‖c‖²=1 for d≥2. Then c satisfies all the cuts (equality), yet does not belong to conv(V∖M): since c is in F it could only use remaining vertices of F, which form a simplex facet missing the center. Therefore if a first nonsimplicial face is such a cross-polytope, the sharp universal cut threshold is exactly d−1. This implication applies beyond root polytopes.

For Q=conv(R), taking polars turns the cut identity into P(M)=conv(P₀∪M); in the ranges where we use duality there is an intact antipodal pair, so 0∈conv(R∖M). Thus the same threshold applies.

## 2. The classical families

For Aₙ (n≥2) the roots are eᵢ−eⱼ on the sum-zero space of n+1 coordinates. Maximizing any nonzero functional exposes all ordered pairs with source in its maximum index set H and target in its minimum index set L. This face is the product of the two simplices on H and L; edge neighbors have dot 1. For n≥3 take |H|=|L|=2 to obtain a square, giving τ=1 by the clipping principle. For A₂ the intact hexagon likewise permits one deletion. To see that two fail, remove e₁−e₂ and e₁−e₃. In the centered A₂ plane their common positive polar direction is now unbounded.

For Dₙ the vertices are ±eᵢ±eⱼ. To expose a proper face, maximize a nonzero functional after making coordinates nonnegative and sorting them. If the largest coordinate is unique and the second largest positive, the face has that fixed coordinate and signs and varies the other index over ties: a simplex. If the second largest is zero the face consists of a translate of the (n−1)-dimensional cross-polytope on the remaining axes. If h≥2 coordinates tie for the largest positive value, the vertices are the sums of two of those basis vectors. This is a point for h=2, a triangle for h=3, and for h≥3 has dimension h−1 by the coordinate differences; h=4 gives a regular octahedron. Thus every edge has dot 1, all two-faces are simplices, and there exists a three-dimensional regular cross-polytope face. Hence τ=2 in every rank n≥4.

## 3. Two exact tests in E₆, E₇, E₈

Use a simple-root chain 0–1–…–(n−2) with node (n−1) attached to 2. Let G denote the Cartan matrix and θ the highest root in simple coordinates.

**Face test.** Fold an exposing normal into the closed dominant chamber and set yᵢ=αᵢ·x. For y≠0 the exposed roots are exactly the positive r attaining θ·y. If Z is the subset of zero y-coordinates, this is equivalent to rⱼ=θⱼ for every j∉Z. Thus at most 2ⁿ−1 masks suffice to cover all proper faces. The checker generates roots by reflections, takes exact affine ranks, checks every edge has dot 1, and locates the first face with more than dim+1 vertices. In each type it finds a regular cross-polytope of the first nonsimplicial dimension: each vertex has dot 1 with all others except for its unique partner with dot 0. This Gram pattern indeed gives the centered orthogonal cross axes: for each paired sum, its inner product with any face vertex is 2; hence all paired sums are the same (their differences are orthogonal to the span of the face vertices). Subtracting their common center gives orthogonal antipodal pairs. The whole polytope is higher-dimensional.

| type | first nonsimplex dimension | example zero-coordinate mask (bit i represents node i) | vertices |
|---|---:|---:|---:|
| E₆ | 4 | 46 | 8 |
| E₇ | 5 | 79 | 10 |
| E₈ | 7 | 254 | 14 |

**Polar test.** Independently use the fact that the positive roots r strictly violating r·y≤1 form an upper ideal in coefficientwise root order. Generate every ideal up to the first failure, intersect its closed inequalities with y≥0 and all retained inequalities, and enumerate all vertices via exact integer determinants. Each cell is bounded since every coordinate occurs in a remaining upper inequality. Up to the stated τ, every vertex is either in P₀ or exactly the arithmetic mean of the roots it strictly violates. By convexity and Weyl symmetry this suffices for arbitrary signed deletions, including non-ideal subsets before folding. At size τ+1 the checker finds a point q separated from conv(P₀∪M) by q itself: ‖q‖² exceeds each q·r for r∈M and exceeds the maximum squared norm of P₀ (so Cauchy bounds its dot against the whole of P₀ strictly). Both the face and polar tests obtain the same sharp thresholds.

## 4. Zero cases and scope

A₁ becomes unbounded after one deletion. In a non-simply-laced Coxeter diagram an edge with label m≥4 gives two signed unit-normal directions at angle π/m; at our normalization their dot product is 2 cos(π/m)>1. Removing just one of these roots does not make it feasible against the other, so it cannot be adjoined on the right of the hull identity. This includes the dihedral, B, F and H cases not already covered above. We normalize *all* mirror normals to the same length: the statement is not about an unnormalized long/short-root convention.

In a reducible simply-laced system, choose r in one component and nonzero w in the intact polar of a different component, supported there and small. The point r+w is feasible after deleting r by orthogonality, but is not in conv(P₀∪{r}): r·(r+w)=2 forces any such convex combination to use r alone. A reducible system with a non-simply-laced component has already failed the one-root test there. This completes the classification.

One application of the identity, by concave hemisphere lifting, is the [robust seven-dimensional kissing bound for a twice-punctured E₆ equator](KissingE6PunctureHull.md). The classification itself does not determine an unrestricted kissing number.
