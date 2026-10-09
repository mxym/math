# Independent Gaussian BV and flux calibration add-on

**Status:** Partial, independent contribution to the Gaussian equal-mass all-k
formalization. The all-k Gaussian first-moment theorem and sharp balanced
multi-bubble perimeter lower bound **remain unproved in Lean**.

Parent checkpoint: PR #3, 136 exact-byte development-compiled modules at
`b6a98c43293d2e80f98dbdccff2b4e86281c36a7`.
Add-on: `GaussianBVFirstMoment.lean`, `GaussianFluxCalibration.lean`,
and `GaussianFluxCalibrationRigidity.lean`. These three modules are
independently added to the lake roots; the parent's
`STATUS.json` and `SOURCE_MANIFEST.json` refer to the frozen 136-module
checkpoint and **do not certify these add-on bytes**. Verification of the
add-on is supplied by the pinned GitHub Actions job for this branch.

## The genuine Gaussian BV first-moment calibration

For every set A in Euclidean Gaussian space, the variational Gaussian BV
perimeter satisfies

    ofReal ||integral_A x d gamma_n|| <= P_gamma^BV(A).

In particular, the theorem concerns the **actual** Bochner Gaussian first
moment, not an arbitrary supplied moment vector. It follows from a
unit-bounded sequence of smooth compact cutoff test fields X_R = -chi_R u
and dominated convergence of their Gaussian divergences.

The theorem is **sharp for every unit-normal halfspace** at any threshold
a: its first moment is phi(a)u and its genuine BV perimeter is phi(a).

Lean declarations:
- `gaussianBVPerimeter_ge_directional_moment`
- `gaussianBVPerimeter_ge_moment_norm`
- `gaussianBVPerimeter_halfspace_eq_moment_norm`

Pinned success: GitHub Actions
https://github.com/mxym/math/actions/runs/37860815416
(Lean 4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612).
All three theorem axiom listings contain only propext, Classical.choice,
Quot.sound; no sorryAx.

## Sharp finite interface Lipschitz calibration

For symmetric nonnegative face coefficients w_ij and actual simplicial
Gaussian winning-cell first moments

    m_i = sum_j w_ij (v_i - v_j),

a label calibration (q_i)_i of pairwise diameter at most one satisfies

    sum_i <q_i,m_i>
      <= (1/2) sum_i sum_j w_ij ||v_i-v_j||.

The right-hand side is the **actual intrinsic Gaussian erosion perimeter**
of the full simplicial winning cluster. The formalized input is the existing
exact moment/face-flux representation, not an assumed regularity condition
or a replacement for the multi-bubble theorem.

The calibration is attained when all score edge lengths equal a>0 and
q_i=v_i/a. In addition, the exact edge gap is

    S - sum_i <q_i,m_i>
      = (1/2) sum_{i,j} w_ij
          (||v_i-v_j|| - <q_i-q_j,v_i-v_j>).

Every summand is nonnegative for a unit-diameter calibration. If all
off-diagonal w_ij are strictly positive, equality forces face-by-face
saturation of the inner-product inequality.

Lean declarations include:
- `symmetric_flux_pairing`
- `symmetric_flux_pairing_le_perimeter`
- `symmetric_flux_calibration_equality_for_equal_edges`
- `actual_simplicial_flux_calibration`
- `actual_equal_edges_flux_calibration_equality`
- `symmetric_flux_calibration_gap`
- `symmetric_flux_calibration_equality_edges`

Pinned successful builds for the flux calibration and exact facewise gap:
https://github.com/mxym/math/actions/runs/37861545962
https://github.com/mxym/math/actions/runs/37861843048
Their #print axioms lists only propext, Classical.choice, Quot.sound.

## Calibration equality rigidity

Suppose the full equal-mass simplicial winning cluster has distinct
independent scores v_i, and a diameter-at-most-one family q_i attains the
face-flux calibration exactly. Because all its off-diagonal Gaussian facet
weights are strictly positive, the exact deficit identity forces equality
on every individual edge. Cauchy--Schwarz equality (with the unit diameter
constraint) identifies each calibrated label difference with the unit
normal of that edge:

    q_i - q_j = (v_i-v_j)/||v_i-v_j||.

Summing this over every three oriented edges gives the actual triple
unit-normal balance. The existing Lean theorem
`all_triple_balances_regular_gram` then forces, for k >= 3 under score
centering and trace-one normalization,

    scoreGram v = regularCovariance k.

The reverse direction is constructive: for regular scores, setting
q_i=v_i/a where a>0 is their common edge length gives diameter exactly
one and attains the calibration. Thus saturation by *some* admissible
calibration is **equivalent to regularity** (among centered trace-one full
winning simplices with k >= 3).

Main Lean declarations:
- `unit_normal_of_inner_saturation`
- `actual_simplicial_saturated_flux_unit_edges`
- `actual_simplicial_saturated_triple_normal_balance`
- `regular_gram_of_saturated_simplicial_calibration`
- `saturated_simplicial_calibration_iff_regular_gram`

The forward rigidity chain passed pinned CI
https://github.com/mxym/math/actions/runs/37862317755
and the reverse implication/biconditional also passed pinned CI
https://github.com/mxym/math/actions/runs/37862609291.
Their owned theorem axiom listings contain only the standard propext,
Classical.choice and Quot.sound axioms, with no sorryAx.

## Scope and remaining major obligation

The above inequalities are sharp at the regular fan **as calibrations**,
but neither proves

    (total intrinsic perimeter)^2 >= (d+1) c_(d+2)^2 / 2

for **all** canonical equal-mass full simplicial winning clusters.
The general balanced Gaussian BV multi-bubble lower bound and the
cluster compactness/regularity dependencies remain unproved. We have not
added an axiom, admitted theorem, or substitute hypothesis for these
obligations.

## Build

From `formalizations/gaussian-simplex-all-k-progress`, with the official
pinned dependencies:

    lake exe cache get
    lake build
    lake env lean sources/GaussianBVFirstMoment.lean
    lake env lean sources/GaussianFluxCalibration.lean
    lake env lean sources/GaussianFluxCalibrationRigidity.lean

The branch workflow performs the build and axiom printing. Parent
module development attestations remain scoped to their original bytes.
