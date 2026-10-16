# Actual symmetric support of pure iid inputs

This package constructs the symmetric support directly in the original complex
coordinate space `Word D k := Fin k → Fin D`, whose computational basis has
`D^k` elements. It uses the pinned Lean 4.34.1 and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The explicit projector averages each occupation fiber. Its Hermitian,
idempotence, exact rank, and pure iid support properties are proved internally.
The occupation index type is Mathlib's multiset type `Sym (Fin D) k`; the
stars-and-bars count is a cited library theorem, not a new combinatorial result.

`SymmetricSupport.PureSpan` proves the reverse inclusion: the actual pure iid
vectors span the entire projector range. Its proof uses evaluation of distinct
complex occupation monomials and the algebraic annihilator theorem.
`SymmetricSupport.UnitSpan` strengthens this to normalized single-system
vectors, proving normalization and homogeneity internally.

`SymmetricSupport.ExactEffect` proves that any actual effect `M` with
`(1-M).PosSemidef` and unit real overlap against every normalized pure iid
density satisfies `M * symmetricProjector D k = symmetricProjector D k`.
This closes the pure-promise to common-support converse without a Haar formula.

`SymmetricSupport.Density` constructs actual pure iid matrices, proves their
positivity, trace and support, and proves that the normalized symmetric
projection is positive with trace one and purity exactly reciprocal dimension.

Key endpoints:

- `symmetricProjector_rank_choose_complement`
- `symmetricProjector_range_eq_unitPurePower_span`
- `purePowerDensity_supported`, `unitVector_trace`
- `symmetricState_trace`, `symmetricState_purity`
- `exact_unitPurePower_effect_mul_symmetricProjector`

Build with `lake exe cache get` followed by `lake build`. Package build outputs
are separate from every predecessor formalization. This scope neither changes
nor enlarges the old 39/91/235/444 or 83/11 audits.

The equality of the normalized projection with a Haar average, general rank-s
Schur support, full universal mixed-state protocols, asymptotic error laws and
circuit gate synthesis are not established by these endpoints.
