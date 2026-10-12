# Actual truncation volume and intrinsic facet geometry

This local subtask proves real geometric identities for the literal
`Entry005.truncationSet d t`. It does not prove the projection-body determinant
sums, the entry-defect rational expression, or the final sharpness theorem.
Those are separate assembly obligations owned by the other agents.

## Statement map and assumptions

Let `K = {x : Space d | (∀ i, 0 ≤ x i) ∧ t ≤ ∑ i, x i ∧ ∑ i, x i ≤ 1}`.

* `Entry005.truncation_actual_volume`: for `0 < d` and `0 ≤ t ≤ 1`, the
  actual Euclidean Lebesgue volume is `(1 - t^d)/d!`.
* `Entry005.truncation_halfspace_representation`: for `0 < d`, the actual
  halfspace intersection with the displayed unit normals and heights is K,
  for every real t. The facet indices are `Fin d ⊕ Bool`, with coordinate
  indices `inl i`, top `inr false`, and bottom `inr true`.
* `Entry005.truncation_top_facet` and `truncation_bottom_facet`: for `0 < d`
  and `t ≤ 1`, these actual facets are respectively the nonnegative-coordinate
  slices of coordinate sum 1 and t.
* `Entry005.truncation_top_facet_area`: for `0 < d` and `0 < t < 1`, the
  actual intrinsic top-facet area, defined as volume of the actual finite
  halfspace facet chart, is `sqrt(d)/(d-1)!`.
* `Entry005.truncation_bottom_facet_area`: under the same assumptions, the
  actual intrinsic bottom-facet area is `t^(d-1) * sqrt(d)/(d-1)!`.
* `Entry005.truncation_facet_area_projection`: for any actual facet index
  and `0 < d`, intrinsic facet area equals the actual projection volume of
  that facet along its own outward unit normal.

The separate coordinate-facet agent proves the remaining coordinate intrinsic
area `(1 - t^(d-1))/(d-1)!` in `TruncationCoordinateFacets.lean`. Combining these
is appropriate for dimensions d≥3 of the paper. This local file does not assert
injectivity of all normals when d=1, where some labels are redundant.

## Proof mechanisms and trusted dependencies

The shell volume is derived from the union with the removed actual simplex.
Their overlap is contained in the actual coordinate-sum hyperplane, whose
ambient volume is zero. The ambient simplex volume is proved by the official
OpenAI/math Tonelli induction, copied unchanged as an exact source prefix into
`TruncationSimplexVolume.lean`. The eight upstream statements and proof bodies
are verified against commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`lean/OAI/Geometry/ProjectionBody/SimplexVolume.lean`; the exact prefix digest is
recorded in `logs/truncation-facet-provenance.json`.

The top area uses the proved actual identity that its radial cone equals the
ambient unit simplex, then the existing kernel-checked radial Fubini formula.
Only the top height is required positive in that formula. The argument never
uses positive bottom cone-law weights: the original bottom support is negative.
The bottom facet is the actual homothety of the top facet. Its area follows
from actual projection-volume scaling and actual negation invariance of the
normal, preserving the real tangent Euclidean measure.

There is no supplied facet area, Jacobian, body volume, or entry-defect identity.
The imported old B bridge remains unmodified. Every exported local statement
and every reused upstream statement has an explicit `#print axioms` invocation
in `formal/audit/truncation-facets.lean`. All 27 exported closure reports contain
only `propext`, `Classical.choice`, and `Quot.sound`. These are standard
propositional extensionality, classical choice, and quotient soundness.
There is no `sorry`, custom mathematical axiom, native evaluation proof shortcut,
kernel check bypass, or linter suppression in these sources or diagnostics.

## Reproduction and local evidence

`python3 scripts/check-local-facets.py` compiles the three source modules into a
fresh local output directory using pinned Lean 4.34.1 and the existing pinned
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 dependencies. It then verifies all
27 exported signatures/axiom reports and the actual module-owned declaration
closures, including private/generated declarations, using Lean's transitive
axiom collector. It does not silently treat this local build as an independent
all-source build of the other project modules.

Successful final logs are `logs/truncation-facet-clean-build.log`,
`logs/truncation-facet-27-signatures-axioms.log`,
`logs/truncation-facet-owned-axioms.log`, and
`logs/truncation-facet-verification.json`. The root task performs the full
project clean compilation and final retrieval bundle.
