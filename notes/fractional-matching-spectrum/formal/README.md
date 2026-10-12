# Formal coverage and source reuse

Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
are pinned together with all transitive dependencies.

FrontierCertificate.lean is copied byte for byte from public
c5255aaf66f9e894c6cbb0e2d1eb47c738c23765. Its nine checked exports
are prior repository work, not new exports counted again. The frozen
manifest records both the payload and explicit source lineage.

Three additional exports in Spectrum.lean use only propext,
Classical.choice and Quot.sound:

- `anchored_frontier` derives the finite max bound from actual vertex
  incidence, feasibility and a maximum-weight anchor meeting every
  edge. Pairwise intersections between the other edges are not a premise.
- `anchor_pair` proves the two-edge feasibility bound from their common
  vertex and an actual subset sum.
- `anchored_half_bound` proves the half bound on actual finite groups
  using that pair constraint and maximum-weight anchor.

The greedy partition and matching-count existence argument, the real
spectrum, unit-interval convex reduction, discrete balancing, concavity,
LP duality and common-rank design constructions are not formalized
in these exports. The full manuscript proves these additional steps.
There is no `sorry`, `native_decide` or extra axiom in either source.

`./bootstrap.sh` preserves the manifest, gets only the required pinned
Mathlib cache, compiles the frozen base and checks Spectrum.lean.
It never runs `lake update`. The shared cloud dependency cache is ignored
by git and is not required for a fresh checkout. The official Lean
compiler, kernel and dependency build machinery remain trusted.
