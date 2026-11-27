# One-point spike out of a simplex: face-sensitive polar and Santaló asymptotics

This note documents the calculator's local asymptotic formula for one moving point. It does not claim a new solution to Mahler's conjecture or a general-purpose proof method. For context, Meyer–Reisner [treat polytopes with at most n+3 vertices](https://arxiv.org/abs/math/0606305), and Kim–Reisner [prove local simplex stability](https://arxiv.org/abs/1001.0217). The calculation here distinguishes whether the moving point starts on a facet, an edge, or a vertex.

## Setup and claims

Set m=n+1, H={x in R^m: sum x_i=0}, v_i=e_i-(1/m)1, and S=conv(v_i), a regular simplex of dimension n. Fix I, 1<=k=|I|<=n, J its complement, and two real vectors lambda,a with sum lambda_i=1, lambda_i>0 for i in I and zero otherwise, and sum a_i=0. Let w(t)=sum (lambda_i+t a_i)v_i and K_t=conv(S,w(t)). Assume some a_j<0 for j in J. Let gamma be uniform barycentric coordinates of the (n-k)-simplex on J (a single point if k=n), and write b(gamma)=(-sum_{j in J} a_j gamma_j)_+. Put

C = n! / [(n-k)! k! prod_{i in I} lambda_i],
B = sum_{j in J} (-a_j)_+,
Y(gamma)_i = 1 for i in I, Y(gamma)_j = 1-m gamma_j for j in J.

As t decreases to zero through positive values, with s_t the Santaló point of K_t and Q=S^circ,

|K_t|/|S| = 1+B t (exact for small t);
|Q \ K_t^circ|/|Q| = C E[b^k] t^k + O(t^{k+1});
s_t = (C/m) E[Y b^k] t^k + O(t^{k+1});
(|K_t^circ|-|(K_t-s_t)^circ|)/|Q| = (C²/2) ||E[Y b^k]||² t^{2k} + O(t^{2k+1}).

The minimal polar factor satisfies |(K_t-s_t)^circ|/|Q|=1-C E[b^k]t^k+O(t^{k+1}); hence the optimized volume product relative to that of S is (1+Bt)(1-C E[b^k]t^k+O(t^{k+1})). For k>=2, the exact first-order increase is B t and the first-order dual loss vanishes, but the leading higher-order dual loss and the optimized translation are both explicit; their exponent k distinguishes the base face. Since Y_i=1 on I and E[b^k]>0 whenever some a_j<0, the optimal center genuinely moves at order t^k. The negative facet volumes sum because the part of K_t outside S decomposes, up to measure-zero boundaries, into pyramids over the facets visible from w(t); their volumes relative to S are minus the corresponding negative barycentric coordinates.

## Exact integral and proof

Use polar barycentric coordinates beta_i=(1-y_i)/m. The convention of Euclidean Lebesgue measure on H makes uniform y in Q equivalent to uniform beta on the standard simplex. The removed region R_t is precisely sum_i (lambda_i+t a_i) beta_i<0. In coordinates beta_I=delta and beta_j=(1-sum delta)gamma_j for j in J, normalized uniform measure is [n!/(n-k)!] (1-sum delta)^{n-k} d delta times uniform measure on gamma. This follows by computing the Jacobian for the remaining n-k independent beta coordinates and integrating gamma, or from a uniform Dirichlet density.

Set delta_i=t r_i/(1+t sum r), beta_j=gamma_j/(1+t sum r). The removed region is r_i>=0 and sum_i (lambda_i+t a_i) r_i < b(gamma); an empty region whenever b=0. Normalized measure becomes [n!/(n-k)!] t^k (1+t sum r)^(-m) d r times uniform gamma, by the rank-one determinant formula. Set rho_i=(lambda_i+t a_i)r_i to fix the domain: rho_i>=0, sum rho_i<b(gamma), with all limits independent of t. The multiplicative Jacobian is prod_i (lambda_i+t a_i)^(-1). The domain is bounded uniformly in t (a fixed), so the normalized integrals have convergent real-analytic extensions near t=0 after factoring t^k. The limiting y there is Y(gamma); the rho-simplex has volume b^k/k!. This proves both the removed-volume expansion and integral (1/|Q|) int_{R_t} y dy=C E[Y b^k]t^k+O(t^{k+1}). More generally this exact integral computes any smoothly weighted cut moment. For k=n (spike through facet interior) it has gamma a point; for k=n-1 the expectation is a one-variable integral with at most one breakpoint.

Translation z maps y in K_t^circ to y/(1-<y,z>) in (K_t-z)^circ, with Jacobian (1-<y,z>)^(-m). Thus F_t(z)=|(K_t-z)^circ| is F_0(z) minus the integral of this same Jacobian over R_t. Both expressions are analytic near z=0, t=0 by the fixed-domain representation. The first z derivative at zero equals -m int_{R_t} y dy, since Q has centroid zero. The Hessian at t=z=0 on H is m(m+1) int_Q yy^T dy. The uniform barycentric moments E[beta_i beta_j]=(1+1_{i=j})/[m(m+1)] give E[yy^T]|_H=m/(m+1) Id, so Hessian=m²|Q| Id. The implicit function theorem gives a local zero of the gradient and expansion s_t=(1/(m|Q|))int_{R_t} y dy+O(t^{2k}); this zero is the unique global minimizer as polar volume is strictly convex on int(K_t), by the same projective formula (strict positivity of the Hessian). Taylor expansion using H_0 and gradient gives improvement equal to (1/2)<gradient,H_0^{-1}gradient>+O(t^{3k}), which yields the claimed expansion with overall error O(t^{2k+1}). Translation formula follows either by direct halfspace rearrangement or polar duality: <y/(1-<y,z>),x-z><=1 iff <y,x><=1 when the denominator is positive.

## Check: through a vertex in the affine-simplex direction

For k=1, if all a_j<=0 on J, then b is affine nonnegative; C=n, and n E[b]=B. First-order primal and dual terms cancel, as they must: v_i for I={i} lies in conv(w(t),{v_j:j in J}) and K_t is an affine simplex. If some a_j>0 and some a_j<0, then B-C E[b]=n E[sum_{j:a_j<0}(-a_j)gamma_j-b]>0. This is a direction-sensitive positive linear coefficient (not uniform as a direction approaches an affine degeneracy). Example k=n, a_j=-1 for the missing j, lambda_i=1/n, gives normalized leading polar loss n^n t^n, in agreement with the simplex cap homothety.

## Remaining prior-art and extensions

The single fixed-center cut is a standard simplex spline/Dirichlet computation in principle. The independent value of the note is the coupled explicit optimal-center and optimization-deficit coefficients, or the exact common projective integral. Do not publish as novelty without a targeted literature comparison about asymmetric stability constants, simplex cap splines and projective derivatives of the Santaló point. Candidate extension: for finitely many spikes anchored on the same face, replace the rho simplex by a bounded union of such regions using r-coordinates, without assuming disjointness. Distinct faces need overlap estimates from the union of supporting I sets. Primal volumes for multiple spikes require separate envelope analysis; no claim made here.
