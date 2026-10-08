# Scope and proof audit

Theorem 1 covers **all measurable** Gaussian partitions of four cells of
mass 1/4, d>=3. Laguerre structure is proved from attainment and linear
assignment, not assumed for competitors. The conclusion concerns only
maximizers: arbitrary equal-mass partitions can have rank one or two.

The key review items are explicit in the paper:

1. Lemma 4 requires an unused Gaussian coordinate. It is used only when
   rank two and d>=3, never to assert extra variations in a saturated space.
2. Edge weights are A_ij/|m_i-m_j|, using unnormalized moments. The
   second derivative has no extra factor two; H's derivative does have two.
3. Minimizing prices are differentiated on the common-price quotient.
   Graph connectivity makes the price Hessian invertible on that space.
   Fourfold planar vertices have codimension two and do not invalidate the
   second derivative. A codimension-one triple tie would force a zero cell.
4. W=P-L is positive semidefinite and kills three independent vectors in
   the rank-two case. Its rank-one factorization has nonnegative coefficient.
5. The two Radon diagonal facets cannot both exist. A missing same-sign
   diagonal contradicts the factorization. No generic triangulation assumption
   is used, and the fourfold-vertex case is included.
6. For a nonvertex moment, zero convex-combination coefficients are allowed.
   The t=0 branch is covered. Merging gives an unconstrained three-cell
   competitor; it is not falsely claimed to retain equal masses.
7. The single-cell Gaussian isoperimetric theorem is an explicit standard
   imported analytic dependency. The three-cell bound is proved in the note.
   The strict profile estimate is derived with rational Taylor bounds.
8. Origin conicity is a conditional assumption in Theorem 2. It is not
   inferred from the fact that a full-rank partition has a common apex.
9. Equal normal-cone areas give face-angle sums pi. The planar unfolding
   proves a disphenoid; it does not by itself prove a regular tetrahedron.
   The final regularity follows separately from equal facet-weight ratios.
10. Theorem 3 is local. Its implicit-function proof has no specified radius
    and cannot exclude far-away noncentral solutions. Its nine equations
    include three mass constraints and six stationary weights.
11. The compact domain (25) is in scores and prices, not apices. Pair
    separation uses an exact-mass median replacement within their union;
    the projected Gaussian subdensity has a uniform density cap. No
    claimed lower singular-value bound follows from pair separation.
12. Local optimality is proved separately through the negative Hessian
    of H, not inferred from stationary isolation. Passing from H to an
    arbitrary competitor uses its normalized moment list and the exact
    linear assignment; the two objectives are not silently identified.

Five Lean exports check the Radon scalar contradiction, the projection
lower bound, interior elimination, rational Taylor margin and the full
linearized algebraic isolation argument. The analytic hypotheses are not
encoded Gaussian theorems. Empty-kernel replay checks their actual dependency
closures under only propext, Classical.choice, Quot.sound; the deliberately
false control must be rejected. Exact rational experiments are diagnostic,
not substitutes for the universal written proofs or the Lean theorems.

The Plackett code is floating point. Both batches converged to the regular
root, with no proof of search-space coverage; a broad run generated an
IntegrationWarning. No result relies on solver output. No external expert
has reviewed this AI-assisted note. This audit is an internal structured
review, not independent professional peer review.

The subsequent covariance route has a full derivation of its Hessian
and conditional global implication in GLOBAL_COVARIANCE_ROUTE.md. The
sign inequality R6, even restricted to the radial direction R7, is still
unproved. The minimum over prices is essential: the explicit diagnostic
detects a substantially different Hessian if prices are held fixed. The
500 floating covariance cases have no interval-certified prices, CDFs,
eigenvalues, or search-space cover. Near degenerating covariances a small
computed positive eigenvalue can be roundoff. Neither these experiments
nor a neighboring unpriced Gaussian-maximum theorem resolves R6.

After environment restoration, the existing five algebra exports were
freshly recompiled using all nine pinned Lake dependency revisions. The
empty-kernel replay again checked 11,769 declarations, rejected the false
control, and produced logs byte-identical to the earlier replay. This is
a refreshed validation record, not new formalization of Gaussian analysis.
