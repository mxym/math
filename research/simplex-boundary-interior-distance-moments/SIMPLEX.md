# Boundary versus interior distances on simplices: a dimension threshold

Let S be a nondegenerate d-dimensional Euclidean simplex, I,I' independent uniform volume points, B,B' independent normalized surface-area points. For d=2,3, every linear functional l and every threshold t≥0 satisfy
$$
\mathbb{E}(\ell(B-B')-t)_+ \ge \mathbb{E}(\ell(I-I')-t)_+. \tag{1}
$$
Both differences have symmetric laws; equivalently, the projected difference of surface points dominates the projected difference of volume points in convex order. In particular for every real p≥1,
$$
\mathbb{E}|B-B'|^p\ge\mathbb{E}|I-I'|^p. \tag{2}
$$
for the Euclidean norm. In dimension one (1) also holds, because a uniform interval point is the conditional mean of a random endpoint, and two independent copies can be coupled independently.

Conversely, in every dimension d≥4 and for each fixed 1≤p<d(d−3), there exist nondegenerate d-simplices *strictly reversing* (2). Thus precisely dimensions 1,2,3 have the comparison for all simplices and all powers p≥1. We do not classify the remaining powers in the higher dimensions, nor all planar convex bodies. In (1) the projection can be multiplied by any scalar, but no multidimensional convex order is asserted. The positive direction is computer-assisted by finite integer arithmetic.

## Projected laws

Write the ordered projected vertex coordinates as x₀,…,x_d. We first assume strict inequalities, achievable by perturbing the functional. Write D_i=∏_{j≠i}(x_i−x_j). For each facet opposite vertex i, let q_i denote its surface weight. The argument even allows arbitrary q_i∈[0,1/2] summing to 1, with conditional uniform distribution on the chosen facet. Indeed the actual area weights satisfy ∑q_i n_i=0 by the divergence theorem for constant vector fields (n_i outward unit normals), so q_i≤∑_{j≠i}q_j.

The barycentric coordinates of an interior uniform point are uniform Dirichlet on the full probability simplex and those of the uniform point on facet i are uniform on the simplex with coordinate i omitted. Put M=∑q_i x_i. The mixture distribution of projected facet points depends only on M. One way to see this and its sign consequence is to take the interior origin O with barycentric coordinates q. The cone from O to facet i has relative volume q_i. Thus I=O+R(B−O) in law with independent R of density d r^{d−1} on [0,1]. This remains true for zero weights by approximation. Differentiating r^d f(M+r(b−M)) and integrating gives, with Z=ℓ(I), W=ℓ(B),
$$
\mathbb{E}f(W)=\mathbb{E}\left[f(Z)+(Z-M)f'(Z)/d\right]. \tag{3}
$$
Let h denote the projected interior density. For distinct knots it is continuous, piecewise polynomial, absolutely continuous and zero at both endpoints in d≥2 (also follows from the divided-difference formula below). Consequently the derivative of the law of W with respect to M is the signed density h'/d by (3). The coefficient of M² in the stop-loss energy of W,W' is
$$
d^{-2}\int (x-y-t)_+h'(x)h'(y)\,dx\,dy
=-d^{-2}\int h(y+t)h(y)\,dy\le0,
$$
by integration by parts twice (or by smooth convolution followed by a limit). A concave quadratic has its minimum at an endpoint of the possible M interval. With each q_i≤1/2 this interval runs from (x₀+x₁)/2 to (x_{d−1}+x_d)/2. Reflection x↦−x interchanges the endpoints and preserves the difference energy by symmetry. Translate x₀=0 and it suffices to take M=x₁/2.

## Exact piecewise polynomial

The elementary simplex divided-difference formula is
$$
\mathbb E f(Z)=d!\sum_{i=0}^d F(x_i)/D_i,\qquad F^{(d)}=f.
$$
Indeed the dth divided difference is the integral of the dth derivative at the barycentric combination over the standard Lebesgue simplex (mass 1/d!): the recursion follows by integrating along the coordinate between the first and last vertices and applying the fundamental theorem of calculus. This applies by approximation to truncated powers. For facet j the denominator at vertex i≠j is D_i/(x_i−x_j); mixing gives the multiplier ∑_j q_j(x_i−x_j)=x_i−M. Apply the formula in both independent variables to (x−y−t)_+, with primitive in x,y involving the positive part to power 2d+1 for I and 2d−1 for B. Thus their energies are respectively
$$
\frac{(-1)^d(d!)^2}{(2d+1)!}\sum_{i<j}\frac{(x_j-x_i-t)_+^{2d+1}}{D_iD_j},
\qquad
\frac{(-1)^{d-1}((d-1)!)^2}{(2d-1)!}\sum_{i<j}
\frac{(x_i-M)(x_j-M)(x_j-x_i-t)_+^{2d-1}}{D_iD_j}. \tag{4}
$$
Zero terms at t=0 are harmless. Their comparison, after multiplying by a positive factor and the squared Vandermonde, reduces to nonnegativity of the following homogeneous polynomial on each sign cell. Write L_ij=x_j−x_i for i<j, w_ij=L_ij−t, X_i=2x_i−x₁, use only pairs with w_ij≥0, and sum
$$
(-1)^{d-1+i+j} w_{ij}^{2d-1}
\left((2d+1)X_i X_j+2d\,w_{ij}^2\right)
\prod_{u<v}L_{uv}^{2-\mathbf 1_{\{i\in\{u,v\}\}}-\mathbf 1_{\{j\in\{u,v\}\}}}. \tag{5}
$$
Indeed the interior coefficient magnitude divided by the facet coefficient magnitude in (4) is d/[2(2d+1)]. The signs in the denominator follow from sgn(D_i)=(-1)^{d−i}.

## Small exact certificate

Run `python3 -B -O verify.py`. Its independent variables are d consecutive gaps and t, all ≥0. For each of the 2^{d(d+1)/2} sign lists of w_ij, intersect the signed inequalities with the nonnegative orthant. Outside full-dimensional cells it suffices to take closure, since (5) is continuous across knots and thresholds. The all-inactive region gives zero. The remaining cones are pointed; every extreme ray is the common nullspace of d independent constraint normals (in dimension d+1). Enumerate all d-fold intersections, choose both orientations and keep exactly the feasible rays. Triangulate the cone by intersecting with the coordinate-sum-one plane, choosing the first vertex and coning over every facet not containing it; apply the same recursion on each face. Every such facet is cut out by one of the original inequalities. This yields 4 simplicial cones in d=2 and 15 in d=3. On each, substitute a nonnegative linear combination of its integer rays into (5), multiply the linear forms exactly, and verify that all coefficients are nonnegative (74 and 4464 positive coefficients, respectively). All exponents fit in base 16 since the total degree d(d+1)+1 is ≤13. Coordinates on an extreme ray may coincide; no denominators survive in (5). For strictly separated knots division by the squared Vandermonde is legitimate; for coincidences take limits of projections with distinct knots in (1), using bounded convergence.

For projected powers, symmetry and the representation x^p=p(p−1)∫₀^∞(x−t)_+t^{p−2}dt for x≥0, p>1 give all p; p=1 uses t=0. Averaging over unit directions, ∫|u·z|^p du is a positive constant times |z|^p, which proves (2).

## Two colliding vertices

In ℝ^d use coordinates (x,y,z) with y∈ℝ^{d−2}. Choose affinely independent y₁,…,y_{d−1}. Take base vertices (0,εy_j,0) and two vertices (1,0,±δ), with ε,δ>0. This is a genuine simplex. For fixed ε let δ↓0: the two facets omitting one of the latter vertices converge to the same nondegenerate (d−1)-simplex; all others degenerate. Thus the two former area weights tend to 1/2 each. Under volume sampling the first coordinate has law Beta(2,b), b=d−1, the sum of the two distinguished Dirichlet coordinates. In the limiting surface law it has law Beta(1,b), by omission of one of them. Then let ε↓0. All transversal distances vanish uniformly, so the two Euclidean p-moments converge to the respective absolute-difference moments of these two beta laws. Iterated limits suffice to produce finite ε,δ with a strict inequality.

Let Y,Y' be iid Beta(1,b) and X,X' iid Beta(2,b). Since the second density is (b+1)x times the first, the ratio of the two p-distance moments, interior divided by boundary, equals (b+1)^2 times the expectation of YY' under the |Y−Y'|^p tilt. In the ordered variables 1−Y,1−Y', write their maximum as U and minimum as UV. The Jacobian U and the tilt U^p(1−V)^p show that under this tilt U and V are independent Beta(2b+p,1) and Beta(b,p+1), respectively. Consequently the ratio is
$$
d^2\,\mathbb{E}[(1-U)(1-UV)]
=\frac{d^2(1+p/2)}{(d+p/2)(d+p)}.
$$
For p>0 this exceeds 1 exactly when p<d(d−3), proving the asserted reversals. In particular, a 4-simplex already reverses the mean distance comparison, whereas every tetrahedron obeys all projected comparisons above.
