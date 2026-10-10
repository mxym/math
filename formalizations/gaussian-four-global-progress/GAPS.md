# Complete gap report: global four-cell theorem remains unproved in Lean

This is a proof-obligation inventory, not an assumption file. None of the
statements below is installed as a custom axiom or silently passed into the
proved analytic core. `UnprovedTargets.lean` gives the final original-object
propositions without witnesses.

Use P=I-11ᵀ/4 and K={Q=Qᵀ≥0 : Q1=0, tr Q=1}. For centered score rows v_i,
M Mᵀ=Q, let C(Q) be the attained actual Gaussian balanced assignment value.
The score-space definition is already formalized as `balancedValue`.

## G1. Closed covariance-cone parameterization

Required: define C directly on real positive semidefinite 4-by-4 matrices via
a chosen square root; prove representation-independence, continuity on the
whole cone, and C(sQ)=sqrt(s) C(Q) for s≥0. The analytic continuity and
homogeneity of the actual score value, and equality under identical Gram
matrices in different ambient dimensions, are proved. Selecting the root,
its continuity, the centered-range identification and compactness of K are
not connected in this package.

## G2. Actual Gaussian facet calculus and interior regularity

For each relatively open winning facet Σ_ij in ambient R³, define its actual
Gaussian surface integral A_ij and w_ij=A_ij/||v_i-v_j||, with zero for absent
facets. Define L by (Lz)_i=Σ_{j≠i} w_ij(z_i-z_j).
Required declarations are:

1. B=LM for the matrix B of actual Bochner cell moments, justified Gaussian
   divergence/integration-by-parts including unbounded polyhedral cells.
2. The actual price Hessian equals L; for affinely independent scores it is
   positive definite on the zero-sum price gauge.
3. Smooth balancing prices and smooth C in the positive cone, with
   D C(Q)[H] = (1/2) tr(LH) for symmetric centered H.
4. The actual envelope score derivative is B, with all differentiability,
   integrability and gauge hypotheses proved.

The existing first price derivative and price-duality theorem are not these
second-derivative and surface-measure statements.

## G3. Surface-area passage through singular limits

Already proved: separated limiting scores and converging prices give actual
winning-set integral convergence for every integrable Banach-valued function;
therefore masses and first moments converge. Still required:

- Exclude a codimension-one triple tie in a diagram with four positive masses.
- Parameterize each limiting facet on its normal plane and prove convergence
  of its actual Gaussian surface area, including disappearance of facets.
- Deduce L_n→L_0 with exactly the lower-rank ambient-three-dimensional definition.

Volume/moment dominated convergence alone does not establish these facts.

## G4. Rank-one and rank-two boundary obstruction

Required: no distinct-score balanced four-cell diagram in R³ with actual
self-moments B=M, centered score rank at most two, and L≤P can exist.
The full proof requires the manuscript's rank-one and planar cases, including
all absent-facet and parallel/collinear configurations. The following inputs
must either be proved or explicitly replaced by fully proved alternatives:

- The unrestricted three-cell first-moment inequality with constant 9/(8π),
  as used after merging two cells. An equal-mass three-cell result does not
  have the needed type.
- Actual Gaussian one-cell isoperimetry / perimeter bound at mass 1/4.
- The planar sign/normal-cone argument and the rank-one quantile-interval
  obstruction, with their strict scalar comparisons justified exactly.

The sharp quantile price estimate
|λ_i-λ_j|≤Phi^{-1}(3/4)||v_i-v_j|| is also not proved here. A weaker explicit
price bound from the actual objective suffices for basic compactness but does
not assert this sharper estimate or any missing strict numerical comparison.

## G5. Exact regular-tetrahedron value and strict local maximum

Required: evaluate the actual Gaussian integrals for the central regular
four-cell diagram, prove masses exactly 1/4, moments parallel to the correct
vertices and
F*=12*(arctan(sqrt(2)))²/π³, hence C(P/3)=sqrt(F*).
The Hessian must then establish the manuscript's strict constrained local
maximum near P/3. Neither an algebraic name for F* nor a floating-point
integral establishes this claim. Our exact sqrt(2π)/16 constant belongs to
the pair-separation lemma and is unrelated to this missing evaluation.

## G6. Four-cell Gaussian multi-bubble/perimeter input

Required: formalize the actual four-cell equal-volume Gaussian multi-bubble
perimeter lower bound in the precise class of diagrams used, and the
conversion from the facet flux/spectral relation to the lower bound on every
full-rank critical value of C. The cited Milman–Neeman paper supports the
written argument, but citation is not a Lean proof. No such theorem has been
added as an axiom, and no use of it occurs in the verified roots here.

## G7. Constrained deformation / mountain pass with the correct normal sign

Required: on the compact covariance domain (or its specified smooth
regularizations), prove a boundary-respecting deformation or equivalent
mountain-pass theorem producing a constrained critical point at the required
intermediate value if an additional maximizer exists. The upper-normal
convention must produce the spectral inequality with the correct sign.
Continuity and compactness do not themselves prove this theorem. There is
no unproved flow hidden in the current Lean interface.

## G8. Regularization, spectral inequality and residual production

For the actual regularized objective C_ε(Q)=C(Q+εP/3), supply the construction,
normal-cone calculation, multiplier bounds and the exact relations used in
Theorem 10, including L≤μP and the complementarity relation at the appropriate
regularized/trace-normalized point. Deduce the actual moment residual bound
of order ε μ², then extract score, price and multiplier subsequences with the
required limits.

Already proved: **given those explicit convergences and actual residuals**,
`residual_limit_pair_separation` excludes score collisions,
`residual_limit_multiplier_pos` excludes μ=0 when μ≥0,
`balanced_residual_limit` identifies actual limiting masses and moments, and
`balanced_limit_self_moment` gives a genuine balanced self-induced diagram.
These theorems do not generate the missing critical sequence or its residual
estimate. Their hypotheses are not a substitute for G2/G7/G8.

## G9. Global sharp covariance/score theorem

Required: after G1–G8, prove C(Q)≤C(P/3) on all K, with equality only at Q=P/3.
Equivalently, prove the correct normalized score bound with its exact Gram
classification. No theorem of either form exists in this package.

## G10. Complete original-object equality classification

Already proved: any actual balanced positive-energy fractional or measurable
set partition reduces to a centered score list with Σ||v_i||²=1 and
sqrt(F)≤balancedValue(v). At own-score dual equality with distinct moments,
labels equal the actual winning indicators a.e. Null modifications preserve
actual moments. Isometric embeddings preserve actual score laws/values.

Still required: combine a proved G9 with the exact G5 computation; prove
positive-energy distinctness in the equality chain; identify the winning
geometry as an embedded central regular tetrahedron; establish both
implications of the a.e. classification, with arbitrary relabeling and
orthogonal-complement extension. The zero-energy case must be separated
using positivity of the sharp constant. These are the proof obligations in
`FourCellFractionalTarget` and `FourCellMeasurableTarget`.

## Completion and release gate

The remaining gaps include deep analytic and geometric results, not only
compilation or packaging. This package is **partial formalization**, even if
all its own proof roots pass source compilation, audit, replay and independent
CI. No immutable Release or DOI, and no claim of the complete Lean theorem,
is justified until both final propositions have unconditional proofs and the
whole enlarged dependency closure passes the required checks.
