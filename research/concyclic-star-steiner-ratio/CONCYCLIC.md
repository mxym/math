# A sharp 4/π bound for arbitrary concyclic inputs, including off-center weighted medians

**Scope.** For any finite set of distinct points P on any circle in the Euclidean plane and any nonnegative demand weights μ totaling one, the minimum cost with a center in P is at most 4/π times the minimum cost over the entire plane. Zero demands may be discarded (removing candidate centers cannot lower the minimum). No assumption that the circle is centered at the geometric median or that the angular gaps are equal. This gives the conjectured unrestricted constant in this subclass, not its conjectured finite-cardinality improvement and not the full planar conjecture. Regular polygons as the cardinality grows show sharpness in this class. This comparison is the short, cardinality-free companion; see FINITE.md for the sharp fixed-cardinality theorem. No priority claim.

## Inversion and its dual weights

In fact fix *any* reference center o. If o is a candidate, its cost is available and the claim follows since 4/π>1. Otherwise translate o to zero. Write r_i=|p_i|>0 and x_i=p_i/r_i²; then |x_i|=1/r_i and
$$
 |p_i-p_j|=r_i r_j |x_i-x_j|.
$$
It will suffice to construct nonnegative α_i, not all zero, depending only on the inverted point set such that
$$
   \sum_i\alpha_i |x_i-x_j|\le (4/\pi)\sum_i\alpha_i |x_i|\quad\text{for every }j.\tag{1}
$$
Then one samples candidate p_i with probabilities ν_i=α_i|x_i|/Σα_h|x_h|. Its expected distance to each p_j is at most (4/π)r_j, by the inversion identity. Summing against *any* demands proves the claim for this same choice of center probabilities. In particular one may take the reference to be the geometric median. The identity is ordinary Euclidean distance inversion; no change of the original demand law is assumed.

The original circle has equation |p|²−2b·p+c=0 in translated coordinates. After inversion its equation is 1−2b·x+c|x|²=0. If c=0 it is an affine line; none of the finitely many p_i is zero, so every image is finite. Take α to give mass 1/2 to each extreme inverse point. Their separation is L; their average distance to any inverse point in the segment is L/2, while their average distance to the origin is at least L/2 by the triangle inequality. This gives (1), even with constant one. A single-point set is trivial. Otherwise the inverted points lie on an ordinary circle, with some center a and radius R>0.

## Exact positive quadrature at circular nodes

Normalize the latter circle to complex nodes z_i=(x_i−a)/R=exp(iθ_i), in increasing cyclic order, θ_{n+1}=θ_1+2π. Write ζ=−a/R for the image of the reference origin, and Δ_i=θ_{i+1}−θ_i in (0,2π). Define positive weights
$$
 h_i=\tan(\Delta_{i-1}/4)+\tan(\Delta_i/4).
$$
They satisfy
$$
 \sum_i h_i|z_i-z_j|=4\quad\text{for each }j,\qquad
 \sum_i h_i|z_i-\zeta|\ge\pi\quad\text{for every complex }\zeta.\tag{2}
$$
Here an arbitrary arc may exceed π; only Δ_i<2π matters. To prove (2), set g_z(t)=|e^{it}−z|. Express it as
$$
 g_z(t)=|e^{it/2}−z e^{-it/2}| = |L_z(\cos(t/2),\sin(t/2))|,
$$
where L_z(u,v)=(1−z)u+i(1+z)v is real linear. On an arc [s,t] with length Δ<2π, the unit vector at half-angle θ/2 is the positive linear combination of the endpoint half-angle vectors with coefficients sin((t−θ)/2)/sin(Δ/2) and sin((θ−s)/2)/sin(Δ/2). The triangle inequality gives the corresponding upper interpolant for g_z. Each coefficient integrates in θ to 2 tan(Δ/4), so
$$
 \int_0^{2\pi}g_z(\theta)d\theta\le 2\sum_i h_i g_z(\theta_i).
$$
When z is a node, L_z has real rank one and its image vector on the open arc has constant sign in that real line because g_z has no zero there. Thus equality holds on every arc even if a zero is an endpoint. In this case the integral is 8. For every z the integral is at least 2π: apply |u−z|+|−u−z|≥2 to opposite unit vectors and integrate. This proves (2) without assuming ζ is interior to the circle, or differentiating at a cusp. Choosing α_i=h_i gives (1), since scaling by R affects both sides equally. ∎

## Sources to distinguish

The exact finite-n upper estimate in the previously studied concyclic case required the circle to be *centered at the Weber point*; a second known upper estimate requires evenly spaced directions. See Dumitrescu, Tóth and Xu, [On stars and Steiner stars](https://adriandumitrescu.org/star.pdf), Corollaries 3 and 4. Neither condition is imposed here, but the constant above is for the class with unbounded cardinality only. [Steinerberger 2026](https://arxiv.org/abs/2602.19311) studies measures with constant distance potential on plane curves and cites Björck's variational theorem: equality on equilibrium support is classical. No claim is made here to introduce distance-equilibrium measures or their general theory. Targeted exact-scope/priority search remains provisional.
