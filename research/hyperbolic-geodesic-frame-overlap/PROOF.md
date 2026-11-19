# Crossing hyperbolic tubes in higher dimension: orthogonal and equiangular extremizers

Let D≥3, N≥2, and δ>0. In curvature −1 hyperbolic space H^D consider N distinct complete geodesics that intersect pairwise at interior points, and let T_i be their closed distance-δ tubes. Use ordinary D-dimensional hyperbolic volume, positive exponent s>0, and the ordered energy E=Σ_{i≠j} vol_D(T_i ∩ T_j)^s.

**Theorem.** Every nonconcurrent family is strictly improvable by a concurrent one. For N≤D exactly the concurrent orthogonal N-frames minimize (one arrangement up to isometry and labels). If N>D and a real unit-vector equiangular tight frame of N vectors in dimension D exists, exactly its concurrent realizations minimize. In particular, for N=D+1 the unique optimizer up to isometry and labels is the set of unoriented directions of a regular simplex at the common point. More precisely, if W_δ(t) is the pair volume at a crossing with squared cosine t, the minimum is N(N−1)W_δ(0)^s for N≤D, or N(N−1)W_δ((N−D)/(D(N−1)))^s in the frame-existence regime. No description of the optimal concurrent directions is asserted when N>D and an equiangular tight frame does not exist.

## 1. Pair geometry and concurrence

Every crossing pair lies in a totally geodesic plane P. In a hyperboloid splitting into the Lorentzian 3-space for P and its Euclidean orthogonal complement, put x=(cosh r · p, sinh r · v), p∈P, v∈S^{D−3}. The induced metric is dr²+cosh²r ds_P²+sinh²r ds_{S^{D−3}}², directly by differentiating the two blocks. For any geodesic L in P, cosh d(x,L)=cosh r cosh d_P(p,L) by minimizing the hyperboloid distance formula over L. Therefore the pair volume, as a function of angular separation θ∈(0,π), is the positive mixture
$$
 V_\delta(\theta)=|S^{D-3}|\int_0^\delta \cosh^2r\,\sinh^{D-3}r\,F_{\eta(r)}(\theta)\,dr,
 \qquad \eta(r)=\operatorname{arcosh}(\cosh\delta/\cosh r).
$$
where F_η is the ordinary planar tube area from #168. For D=3 the two sides are the two points of S⁰. The distance and volume formulas also imply positive finite volume at each fixed interior θ. The functions F_η are strictly angular log-convex and symmetric about π/2 by #168 whenever η>0. Strict pointwise log-convexity and Hölder show that their mixture is strictly angular log-convex, so each positive power of V_δ is strictly angular convex and strictly decreasing on (0,π/2].

Three pairwise-intersecting geodesics that do not concur are contained in their triangle's totally geodesic plane. A geodesic outside that plane meets it at most once, and hence cannot meet all three, as they have no common point. Thus any nonconcurrent pairwise-intersecting family is coplanar. Apply the anchor-collapse triangle comparison of #168 there, with cost V_δ^s in place of F_δ^s, to get a strictly better family concurrent in that plane (hence admissible in H^D). This part does not require a frame.

## 2. Strict log convexity in squared cosine, all powers

For planar half-width η>0, let a=sinh η, b=2a² and h_b(x)=sqrt(1+b/x)−1. The formula of #168 uses 4 times the integral of h_b(2sin²u) from θ/2 to (π+θ)/2. For x>0 we have the exact positive mixture
$$
 h_b(x)=\frac1\pi\int_0^b\sqrt{\frac{b-z}{z}}\,\frac{dz}{x+z}.
$$
Indeed substitute z=b sin²v and write b cos²v=(x+b)−(x+b sin²v). The elementary tangent substitution gives ∫₀^{π/2}(x+b sin²v)^{−1}dv=π/(2sqrt(x(x+b))), proving the identity.

For the reciprocal term h(x)=(x+z)^{−1}, let A=1+z, B=A²−1 and t=cos²θ, taking 0<θ≤π/2. Its angular integral H_z(t) is
$$
 H_z(t)=\frac{4}{\sqrt B}\arctan\sqrt{\frac{B}{1-t}}\qquad (B>0),
 \quad H_0(t)=4(1-t)^{-1/2}.
$$
To verify it, differentiate the moving endpoints. At c=cos θ, the squared sine arguments 2sin²u are 1−c and 1+c. Division by dt/dθ=−2c sin θ gives H_z'(t)=2/[(A²−t)sqrt(1−t)] on (0,1). At t=0, symmetry of the integral about π/2 and the tangent substitution give H_z(0)=8 arctan(sqrt((A−1)/(A+1)))/sqrt B =4 arctan(sqrt B)/sqrt B, by the double-angle arctangent identity (the input to the doubling is in [0,1)). These initial values and derivatives give the formula. For z=0 integrate csc² directly or take the limit.

For B>0 write q=sqrt(B/(1−t)). Then arctan q≥q/(1+q²) by integrating its decreasing derivative on [0,q]. Hence H_z'/H_z≤1/[2(1−t)], whereas H_z''/H_z'=1/[2(1−t)]+1/(A²−t), strictly larger. Since H_z'>0, H_z is strictly increasing and strictly log-convex; so is H_0 by its direct expression. Tonelli interchanges the positive resolvent and angular integrals, and Hölder preserves strict log-convexity under this mixture. The mixture over r also preserves strict log-convexity: interior r has η(r)>0 and positive weight. Thus W_δ(t)=V_δ(arccos sqrt t) is positive, strictly increasing, and strictly log-convex on [0,1). In particular W_δ^s is strictly convex and increasing for every real s>0, not just s≥1.

## 3. Frame equality

At a concurrent point pick unit representatives u_i of the unoriented tangent directions; t_{ij}=|u_i·u_j|². If N≤D all costs attain their individual lower bound exactly when the vectors are orthogonal. If N>D, put S=Σ_i u_i u_i^T. Cauchy–Schwarz on its D eigenvalues gives tr S²≥N²/D, with equality exactly at S=(N/D)I. Subtract N for the diagonal and divide by N(N−1), giving the Welch bound on the average t_{ij}. Jensen for the strict kernel then gives the lower bound of the theorem, with equality exactly when all off-diagonal t_{ij} coincide and S=(N/D)I. These are exactly the real equiangular tight frames, under choices of signs; the spectral and Jensen argument is classical frame theory, not a new frame bound. If N=D+1, any such Gram matrix is (N/D)(I−vv^T) with a normalized null vector v. Its unit diagonal forces |v_i|=1/sqrt N; flipping representatives makes all v_i positive, giving the simplex Gram matrix. This proves the asserted uniqueness and scope.
