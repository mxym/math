# Two punctures in a D₅ or D₆ equator do not raise the kissing bound

**Theorem.** Let a kissing configuration in Euclidean dimension six contain at least **38 of the 40 signed roots of a fixed equatorial D₅**. It has at most **72 points**. If its intersection with those 40 roots has size exactly 39, it has at most **71**, and 71 is attained. In dimension seven the corresponding thresholds for a fixed equatorial D₆ are **58 out of 60**, **126** overall, and a sharp **125** when exactly 59 are present.

The remaining points are arbitrary real points. No full half-spin layer, transversality, underlying E₆/E₇, or antipodality is assumed. In particular every 73-point six-dimensional candidate must omit at least three points of every D₅ equator. This does not determine the unrestricted kissing numbers.

Write n=5 or 6 for the equator dimension, G={±eᵢ±eⱼ : i<j}, and use radius √2, so the upper inner-product bound is 1. Let M be the exact subset of G absent from the code, of size m≤2. Write p₀=n(n−1) for the number of equatorial root axes, and K=36 or 63 for the maximum number of lines in dimension n+1 satisfying |x·y|≤1 at this normalization. We will use the equality case of [Anstreicher's antipodal bound](https://optimization-online.org/2001/01/248/): at K lines the doubled configuration is an orthogonal copy of the E₆ or E₇ root system, respectively.

## 1. A finite certificate for continuous hemisphere lifts

For an outsider (v,z), meaning any code point not in G, its horizontal part v is in the polytope P(M) given by v·r≤1 for every r∈G∖M. Each |vᵢ|≤1: otherwise for each j≠i at least one root on {i,j} is violated, requiring at least n−1 omissions. At a vertex choose n linearly independent tight signed equations. Each has the form vᵢ=±vⱼ±1. Along a connected component these express each coordinate as ±t plus an integer. If no cycle reverses the coefficient of t the equations have a free parameter, contradicting independence. A reversing cycle implies 2t is an integer. Thus the bounded polytope is the convex hull of vertices on the grid 2v∈{−2,−1,0,1,2}ⁿ.

The [exact verifier](verify-kissing-partial-dn-equators.js) checks all feasible half-grid points (a superset of the vertices). For m≤2 they have squared norm at most 2, with equality only at original Dₙ roots. By strict convexity the same holds for the entire polytope. Hence all actual outsiders have z≠0. For m=0 everything below follows by containment in a single-omission polytope. For m=1 or 2, transitivity of signed coordinate permutations lets us fix one omitted root; the inner product k of the two roots and the size t of their support intersection classify the relative possibilities (repeating the root means one omission).

Let h(v)=√(2−‖v‖²). It is nonnegative and concave, being the positive hemispherical height over the ball. Writing two arguments as vertex convex combinations, their lifted inner product v·w+h(v)h(w) is bounded below by the product-weighted average of the vertex-pair lifted inner products. This applies on either fixed hemisphere. The verifier tests the threshold −1 for every pair by integer comparison: if u=2v, u′=2w and d=u·u′<−4, the test is (8−‖u‖²)(8−‖u′‖²)≥(d+4)².

| (k,t) | D₅ feasible grid points | D₆ feasible grid points | ordered pairs below −1, in either dimension |
|---|---:|---:|---:|
| (2,2): one omission | 256 | 744 | 0 |
| (0,2) | 259 | 747 | 0 |
| (−2,2): opposite roots | 259 | 747 | 10 |
| (1,1) | 260 | 748 | 0 |
| (−1,1) | 259 | 747 | 0 |
| (0,0) | 259 | 747 | 0 |

Therefore unless M is an opposite pair, all outsiders in either individual hemisphere are projectively compatible with one another. This only adds the lower bound ≥−1; the upper bound ≤1 for distinct actual outsiders is the kissing constraint.

## 2. The opposite-root exception costs at most one point per side

By symmetry M={r,−r}, r=e₁+e₂. Call an outsider good if neither signed root is violated; otherwise it belongs to the positive or negative group according to which one is violated. Good points are compatible with both groups, and each group is internally projectively compatible, by the single-omission result applied to the appropriate union. Two points in the same hemisphere both of height |z|≥1/√2 are also compatible: their angular distances to its pole are at most 60°, hence their mutual angle is at most 120°.

We show that, within a hemisphere, a low point (|z|<1/√2) in a violating group is its only member. It suffices to consider a positive one X. Both first coordinates are positive, with ordered magnitudes a=1−u≥b=1−w and a+b>1. All n−2≤4 tails have absolute value at most u using the retained roots involving the largest coordinate. Since ‖v‖²>3/2, we have
`2a²+4(1−a)²>3/2`; the two equality roots are 1/2 and 5/6, so a>5/6. Moreover b²>1/2+2u−5u²≥(2/3+u)² for 0≤u≤1/6 (the difference is concave and nonnegative at both ends). Consequently u+w<1/3. The height satisfies
`z² ≥ 2u+2w−5u²−w² ≥ 2(w+2u)².`
For the last inequality the difference is 2u+2w−13u²−8uw−3w², a concave quadratic on the triangle 0≤u≤w, u+w≤1/3; its values at the three corners are 0, 1/3, 0.

If a second positive-group point is low, the first two coordinate products sum to at least 2−(u+w)−(u′+w′), regardless of coordinate ordering. The tails lose at most 4/36, so even the horizontal dot exceeds 1. If the second point Y is high, its first coordinates are positive and sum to more than 1, so their contribution with X exceeds 1−w. Each tail of Y has magnitude less than 1/2, so all tails together lose at most 2u. The height product is at least |z|/√2≥w+2u. Both possibilities contradict the kissing inequality. This proves the isolation claim.

A projective conflict can thus only join opposite violating groups and must involve a low member. If only one group has lows, it has at most one member; if both do, each is a singleton. Deleting at most one outsider per hemisphere destroys all its projective conflicts.

## 3. Count by reflection closure

Let ℓ be the number of fully paired equator axes and take any projectively compatible set of q′ outsiders in one hemisphere. Their lines are distinct from one another and from the equatorial axes, and are projectively compatible with the ℓ paired axes. Thus ℓ+q′≤K.

If m>0, **strictly** ℓ+q′≤K−1. Indeed equality gives an antipodal root system by Anstreicher. It contains the signed roots of the paired axes, which generate all of Dₙ by reflections. One can even write each root x of a lost axis as y+z with y,z from the paired axes and y·z=−1: for x on coordinates i,j use a spare coordinate k and cancel its contributions in y,z. At most one additional lost axis can interfere, so there is an available k (also verified explicitly). Then reflection of z in y is z+y=x. But no lost equator axis is among our ℓ lines or our off-equator q′ lines, a contradiction.

* If m=0, ℓ=p₀, and each hemisphere contains at most K−p₀ outsiders, giving 2K overall.
* For m=1 or two nonopposite omissions, ℓ=p₀−m; each hemisphere has at most K−p₀+m−1 outsiders. Including the 2p₀−m retained roots gives 2K+m−2.
* For two opposite omissions, ℓ=p₀−1; each hemisphere can lose at most one outsider to become projective. It therefore has at most K−p₀+1 outsiders. Including the 2p₀−2 retained roots gives 2K.

Deleting one equatorial root of the standard E₆ (respectively E₇) code supplies the sharp one-omission example. For context, [Novgorodtsev, Theorem 2](https://www.preprints.org/manuscript/202610.0335) bounds and classifies the six-dimensional **full** D₅ cross-section case; here the near-complete equators require neither full layers nor a specified completion.
