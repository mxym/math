# Four equal Gaussian cells: Lean formalization

This project is the source-level formalization workspace for the four-cell
Gaussian first-moment theorem. It imports the actual-Gaussian, covariance,
flux, radial-comparison, and equality-reduction development that was
previously kept in a scratch checkpoint. It also contains kernel-checked
discrete projected-ascent bookkeeping and an unconditional two-cell boundary
case.

The final consequence is exposed in
`GaussianFourCellTheorem.lean`: once the exact simplicial perimeter lower
bound `EqualMassSimplicialPerimeterBound 2` is supplied, Lean proves both the
sharp four-cell upper bound and the almost-everywhere regular-fan equality
classification. This file does not introduce that geometric input as an
axiom. The remaining target for a complete formalization is therefore the
genuine four-cell Gaussian perimeter lower bound (the relevant
Milman--Neeman theorem, or an independent proof of the same statement).
The continuous mountain-pass argument in the manuscript is not a dependency
of this radial-comparison interface; the discrete lemma is retained as an
independent formal record of that auxiliary argument.

The current source already contains the actual standard-Gaussian measure and
Bochner moment layer, price duality and balancing, covariance pushforward,
facet flux, symmetric positive-semidefinite moment Laplacians, regular
tetrahedral attainment, radial comparison algebra, conditional equality
reduction, and the proved two-cell perimeter boundary case. The complete
source project builds successfully with the pinned toolchain; no `sorry`,
`admit`, custom axiom, or numerical oracle is used.

The reproducible build command is:

```text
lake build GaussianProgress
```

The current clean build completes all 3,887 jobs. A trust-zero replay of the
conditional four-cell interface, the unconditional two-cell boundary theorem,
and the discrete ascent theorem reports only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.

Pinned toolchain: Lean 4.34.1 and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
