# Actual pyramid / B / entry-defect formalization

The actual finite-pyramid geometry and the entry005 cone-law bridge are now
kernel checked. The final theorem
`Entry005.actual_body_joint_polar_pyramid_assignment` preserves the main
owner's single compact-limit witness `μ,φ`, its raw law, polar-boundary support
and its existing assignment tuple. A, B, D, brightness and the cost estimate
all refer to that same measure. No geometric identity or independently chosen
measure equality is assumed.

For `K=finiteHalfspaceSet n h`, `V=|K|`, `d=finrank ℝ E`, and the actual
intrinsic facet areas Ai, the proved facts are:

| Lean theorem | Actual mathematical statement |
|---|---|
| `pyramid_finite_halfspace_volume` | `|P(K)|=V/(d+1)` |
| `pyramid_base_facet_area` | actual bottom facet area is V |
| `pyramid_side_facet_area` | actual side facet area is `Ai*sqrt(1+hi^2)/d` |
| `pyramid_projection_body_eq_zonotope` | actual ΠP is the bottom/side facet zonotope |
| `pyramid_projection_body_volume_decomposition` | `|ΠP|=|sideZ|+V/d^d*|ΠK|` |
| `pyramid_side_zonotope_volume_lifted_moment` | `|sideZ|=V^(d+1)/(d+1)!*B` |
| `finite_halfspace_entryA_lifted_moment` | `entryA(K)=B/((d+1)A)` for the actual finite cone law |
| `actual_body_entryA_of_compact_limit` | the same entryA identity for the same actual arbitrary-body compact limit used for A |
| `actual_body_cone_law_with_pyramid_defect` | actual law, brightness, A, B, `D=(d+1)A e`, `D/B=(d+1)e/(1+(d+1)e)` |
| `actual_body_joint_polar_pyramid_assignment` | one polar-law witness and the same assignment tuple, with cost at most `(d+1)(d+2)*(d+1)e/(1+(d+1)e)` |

The side-facet area proof constructs a genuine orthogonal linear isometry,
derives its actual radial chart, applies the real radial Fubini formula and
handles redundant/empty facets and the apex explicitly. No Jacobian or facet
area formula is supplied as a hypothesis. The projection-body computation
uses the proved actual finite Cauchy theorem and true extrusion volume. The
lifted-moment normalization uses the actual height-first law coordinates,
their genuine Euclidean isometry and the exact finite iid determinant moment.

The principal finite formula assumes finite labels, unit injective normals,
strictly positive heights, compact halfspace intersection, positive dimension,
and the displayed finite-dimensional inner-product/Borel structures. V, ΠK
volume and A are proved positive. Individual supporting lemmas have weaker
hypotheses; their literal compiled signatures are all recorded in
`coverage.json`.

The actual general-body existence theorems require a compact convex
`K ⊆ Space d` containing the closed unit ball and `Nontrivial (Space d)`.
Conditional limit leaves explicitly take the actual finite-law weak limit,
the same μ and a strictly increasing φ. The unconditional wrappers construct
these data. The approximation step proves actual pyramid dilation containment
and convergence of the actual projection ratios, and passes A and B along the
same subsequence. Generic iid algebra leaves explicitly state their entryA
premise; the actual geometric wrappers prove that premise rather than assume it.

The exact paper map is the sharp-stability paper's equation `eq:cone`, its
following arbitrary-body approximation paragraph and assignment section, and
entry005 v2 Section 3's pyramid/facet algebra. The frozen current paper is
[mxym/math proof.tex at c897a556](https://github.com/mxym/math/blob/c897a556e12e460380c7cf521e88f84286994915/notes/sharp-simplex-stability/proof.tex).
Every new public export is mapped separately in `coverage.json`, including
supporting mechanisms that are not separately numbered paper statements.

Validation completed successfully:

- 102 delivered mathematical modules freshly compiled from source into an
  initially empty owned-output directory, with zero warnings.
- Every one of the 714 explicit public source theorem names has an actual
  compiled signature, individual `#print axioms` output and matching declaring
  module. This includes reused dependencies; it is not a claim of 714 new results.
- All 1,499 actual module-owned declarations, including private lemmas and
  generated auxiliaries, have their recursive axiom closure checked.
- All 82 new exports pass. Of these, 79 have new proof bodies and three narrowly
  reuse byte-identical iid helper statements and bodies.
- All 26 inherited affine proof-module bytes remain unchanged; its original
  umbrella is also retained. All 56 borrowed owner modules are byte-identical
  to their observed exact source snapshots. The two polar/joint files match
  the owner's published assembly hashes.
- Compiler and all nine dependency Git pins pass both ordinary and Python -O
  checks, with tracked upstream sources clean. Existing mathematical controls
  and ten adversarial audit controls pass.

The only permitted logical axioms are propositional extensionality `propext`,
classical choice `Classical.choice` and quotient soundness `Quot.sound`.
The exact subset for each proof is recorded in the verification JSON.
There is no `sorry`, `admit`, `sorryAx`, custom unchecked geometry axiom,
`native_decide`, native evaluation axiom or suppressed kernel check in the
audited mathematical closure. The diagnostic auxiliary-name linter is disabled
only when inspecting generated names; all kernel checks remain enabled.
The trust boundary includes the official pinned Lean compiler/kernel and the
official pinned mathlib compiled dependency cache. All delivered owned proof
sources were recompiled; the entire mathlib repository was not rebuilt from scratch.

Lean is pinned to 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`; mathlib is pinned to
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The complete lockfile, official
bootstrap and portable clean verifier are included. Original maintained
OpenAI/math source, pins, Apache license and exact adaptation/reuse provenance
are retained. No credentials were added and no network/TLS restriction changed.

This closes the actual finite facet/B bridge and its normalized arbitrary-body
cone-law/defect passage. The full prescribed maximum-simplex quantitative Main
target, final stability exponent and exact constants, geometric equality
classification and full sharpness theorem are not proved by this increment.
Prior 147 geometry statements are not counted as an integrated Main proof.
Parent independent review and assembly remain required. Nothing was pushed,
merged or publicly published.
