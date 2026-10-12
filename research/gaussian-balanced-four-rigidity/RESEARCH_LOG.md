# Route toward a complete equal-mass solution

8 October 2026. This is a route record; statements proved in full are in
paper.md, and numerical observations are marked separately.

The goal remains the global classification over all measurable partitions.
The arbitrary-mass counterexample does not address it. A source check first
separated Heilman's conicity conjecture from the stronger regularity claim.
Unit-variance Gaussian maximum comparison was examined and set aside:
equal mass alone does not prove equal moment lengths or zero prices.

The score formulation permits arbitrary perturbations in an unused Gaussian
coordinate. Its Hessian yields L<=I. Gaussian flux LM=M then gives a
rank-one defect when the moments have rank two. The missing Radon diagonal
excludes convex quadrilaterals. This still left a central bounded cell, so
the argument was continued with Gaussian isoperimetry and a three-cell
merge. A strict rational profile estimate closes that remaining branch.
Ordered interval scores exclude rank one. Thus all global maxima are full
rank; no planar case is left as an unproved assumption.

The full-rank flux equations alone do not imply equal moment norms or a
zero apex. The zero-apex branch was solved separately: equal normal-cone
areas force face-angle sums pi, unfolding gives a disphenoid, and exact
facet-weight comparison gives regularity. The translation parameter is
essential; the argument cannot simply be reused for shifted Gaussian cones.

All nine stationary equations were then written in deterministic Plackett
quadrature form. Two fixed batches, 24 moderate and 32 wider starts, were
run against the published discovery source. They returned the regular root.
One wider run produced an IntegrationWarning. These floating-point root
searches are neither interval enclosures nor a global exclusion certificate.

The equations' full derivative at the regular root was derived analytically.
It separates into diagonal shape, opposite-facet, and mass blocks. Every
block is invertible, proving local stationary isolation. A separate Hessian
calculation proves strict local optimality and transfers its bound to
arbitrary measurable competitors with nearby normalized moments.

The global search variables were made bounded without assuming a bounded
geometric apex: a density-capped median replacement separates every pair
of optimal moments, and halfspace containment bounds every price difference.
This removes two avoidable difficulties for a future rigorous search.

What is still missing is an exclusion of noncentral, irregular full-rank
global maximizers elsewhere in this compact score/price domain. Possible
routes remain a global comparison of opposite facet weights after mass
balancing, or interval branch-and-bound outside a quantitatively certified
regular neighborhood. Neither route currently has the required inequality,
an explicit neighborhood radius, or a finite coverage certificate. No theorem
asserts global uniqueness of the nine-equation root system; even excluding
local maxima must be proved rather than read from the root searches.

The next meaningful endpoint is that exclusion, which would close the
original conjecture using Theorems 1–2. Producing another numerical root
batch or merely optimizing constants would not close it.

The next attempt changes the global formulation. For the balanced value
C(Q), with score covariance Q, permutation averaging would give the sharp
upper bound if covariance concavity held. A separate proof shows that
concavity only along the rays to P/3 would already suffice, including
uniqueness through the established strict local maximum. The full Hessian
was derived by following a linear covariance path, differentiating prices,
and integrating the facet moments. It reduces the problem to the explicit
surface quadratic inequality R6 of GLOBAL_COVARIANCE_ROUTE.md; direction
R7 suffices. This is a precise new possible bottleneck, not a proved sign
inequality or a replacement of the original conjecture by a theorem.

The code evaluates this Hessian from bivariate truncated Gaussian moments
rather than finite differences. A separate finite-difference diagnostic
checks its signs, factor four and necessary price adjustment. Two fixed
covariance batches, 200 and 300 cases, found no eigenvalue above 1e-5;
near-boundary positive values of roundoff size do occur. None are certified
signs. Broader scratch tests with unequal label masses did not settle a
general theorem and are not represented as such. The neighboring unpriced
nonconcavity example in Sun–Hu–Lan was checked at its exact source; it
neither proves nor refutes the fixed-mass covariance property.

The analytic sign question remains open. The branch cannot be closed by
repeating numerical batches. The current objective is to prove the radial
version of R6, find a certified obstruction to this route, or obtain a
different complete global comparison. The earlier algebra-only Lean roots
were meanwhile freshly rechecked against all pinned Lake checkouts, with
the same empty-kernel closure and byte-identical logs.
