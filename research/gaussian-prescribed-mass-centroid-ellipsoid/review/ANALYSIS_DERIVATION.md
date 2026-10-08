# Prescribed-mass centroid ellipsoid: analysis-agent audit

Date: 8 October 2026. This is an internal mathematical/model review, not external
human peer review or complete Lean certification. Source reviewed and frozen:
`PRESCRIBED_QUOTA_ELLIPSOID.md`, SHA256 `777c477aa453d1ad5b5e298564e09bf76764e6d6fa0e2f526d8b9da86a43f0dd`.
The root independently checked the preceding source version (`7cc58e...`);
the final version adds only the elementary profile-Hessian normalization check
in Section 6. Theorems A/B and Sections 1--5 are unchanged.

## Exact scope

All integers k>=2, all positive probability vectors p, all centered Hermitian-free
real PSD covariance matrices Q; all finite ambient dimensions d>=1; every
measurable simplex-valued Gaussian function f with mean p. The analytic input is
the proved Gaussian multi-bubble perimeter theorem in dimension k-1. There is no
floating, integer-degree, limiting-conjecture or heuristic solver premise.

## Independent adversarial checks

1. **Quota prices and translated model.** In the min-price-zero gauge the dual
   objective is >=p_min max(lambda), because a zero-priced mean-zero score is a
   lower bound for the maximum. Thus a minimizer exists for every covariance.
   Full-rank centered scores are affinely independent; all facets have positive
   area at every finite price. The price Hessian is the positive weighted
   Laplacian on 1-perp. This proves unique smooth prices in the zero-sum gauge,
   and identifies their translated regular simplex fan with the established
   perimeter minimizer for exactly the prescribed masses. No ordinary equal-
   mass statement is applied to an unequal quota.
2. **Flux and normalization.** The Gaussian first moments of the winning cells
   are LM. The quota price terms cancel in C, even though the prices need not
   be zero. Therefore C=tr(LQ)=sum w ell^2 and tr L=2sum w. On the trace-one
   regular Gram Q*=P/(k-1), ell*=sqrt(2/(k-1)), c_p=tr L_p/(k-1)=ell* I(p).
   The score Laplacian and interface-area Laplacian differ by ell*: H_p=ell*L_p.
3. **Imported perimeter scope.** The arbitrary positive p theorem is applied
   in dimension n=k-1 where its k<=n+1 hypothesis holds. A general score fan
   has the same label masses and finite Gaussian perimeter. Weighted Cauchy
   gives C tr L/n>=c_p^2. Each weight is strictly positive; equality in Cauchy
   forces every pair edge length equal, regardless of nonuniform p.
4. **Nonzero initial derivative.** On Q_t=Q*+t(Q-Q*) the exact identity is
   t C'=(C-tr L/n)/2. For h=C^2-c_p^2, h'(0)=c_p tr[L_p(Q-Q*)], rather than
   zero. Thus (h/t)'=-(C tr L/n-c_p^2)/t^2<=0 gives
   C_p(Q)^2<=c_p tr(L_p Q). The initial linear term was retained with the
   correct sign and factor. A uniform-only tangent assumption is absent.
5. **Improper integral and singular endpoint.** C is continuous on the closed
   PSD cone by the square-root coupling bound uniform in price. Q_t is strictly
   positive on 1-perp for t<1. The integral equals differences of h/t on compact
   subintervals; its nonnegative integrand and finite endpoint limits give the
   full exact deficit formula. At zero D(t)=O(t^2) follows from smoothness; no
   boundary facet continuity or finite rank-one derivative is needed.
6. **Equality and scaling.** An integral of continuous nonnegative D equal to
   zero forces D=0 at every interior t. Positive-weight Cauchy equality makes
   Q_t=Q*, then Q=Q*. Homogeneity extends the bound and equality to all trace
   s>0; Q=0 is handled separately. No nonzero singular covariance attains it.
7. **Pseudoinverse and functions.** Actual moment columns sum to zero. Choosing
   M=L_p^+ B makes E=<M,B>=tr(M^T L_p M). A feasible fractional score assignment
   pairs at most C_p(MM^T), without asserting unproved primal equality when
   score rows coincide. Hence E^2<=c_p E and E<=c_p. If E=c_p>0 the covariance
   equality gives MM^T=Q*, so all ties are null, and zero pointwise assignment
   deficit forces ordinary winning indicators. Unique model prices classify
   all equality functions and make low-dimensional strictness explicit.
8. **Profile-Hessian metric.** Independently D_lambda mass=-L_p and
   D_p lambda=-L_p^+ on the centered label space. The price envelope gives
   grad_p c_p=lambda, so Hess c_p=-L_p^+ and Hess I=-H_p^+.
   This agrees with the published Milman--Neeman Proposition 2.4. No extra
   factor 2 or edge-length convention enters the final formulation.

## Result of audit and limitations

No substantive mathematical gap identified in this derivation. The centroid
ellipsoid is sharp and applies to arbitrary partitions and fractional functions.
It does not solve the false ordinary unweighted unequal-mass moment conjecture.
Global novelty and literature priority are not established by this audit. A new
Lean proof of the abstract nonzero-initial-slope radial comparison is being
checked separately; it does not formalize Gaussian score calculus, perimeter
minimization or the full theorem.
