# Scope of the Lean verification

Lean 4.34.1 and all transitive dependencies are pinned by the toolchain
and lake-manifest.json. Mathlib revision:
d13f23b723b8a846827a245b89c10fc7d3f11612.

Seven checked exports use only propext, Classical.choice and Quot.sound:

- `weighted_star` derives the peak-edge inequality from actual finite
  edge sets, an r-vertex edge, pair intersections, nonnegative real
  weights and all vertex feasibility constraints.
- `threshold_degree` derives the degree cap of the threshold core.
- `bad_mass_bound` sums the real peak deficits over the deleted edges.
- `extraction_algebra` combines the peak and average inequalities.
- `incidence_extraction` obtains the cross-multiplied finite deletion
  bound from actual intersecting uniform incidence and feasible weights.
- `capped_core_feasible` constructs the 1/k weights on a degree-capped
  core and verifies feasibility on the whole original family.
- `capped_core_mass` proves their objective value is q/k.

The last two constitute the finite converse used in Theorem 3. They
do not assert that an LP optimum or an integral cover has been found.
The positive-denominator division, explicit design-boundary coefficient,
degree/excess identities, limits, LP duality, sharpness construction and
published rounding input are outside these formal exports. Their full
written arguments are in paper.md; no unproved Prop is presented as a
formal theorem. There is no `sorry`, `native_decide` or extra axiom.

Use `./bootstrap.sh` for a fresh checkout, then
`lake env lean DesignCore.lean`. The manifest is preserved; bootstrap
does not run `lake update`. The shared package cache used in this cloud
session is ignored by git and is not a reproducibility dependency.
The official Lean compiler, dependency builds and kernel implementation
remain trusted; no external kernel implementation or human review is
claimed.
