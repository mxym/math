# Four equal Gaussian cells: Lean formalization

This project is the source-level formalization workspace for the four-cell
Gaussian first-moment theorem. It imports the 140-module actual-Gaussian,
covariance, flux, radial-comparison, and equality-reduction development that
was previously kept in a scratch checkpoint, and adds a kernel-checked
discrete projected-ascent lemma for the mountain-pass step.

The main theorem is not yet marked complete: the remaining mathematical input
is the sharp equal-mass Gaussian multi-bubble/perimeter lower bound (the
Milman--Neeman four-cell case), together with the final continuous projected
deformation interface. No axiom or `sorry` is used to hide this input. The
formalization will be marked complete only after that lower bound and the
deformation chain are proved and the full source closure is replayed in an
empty kernel.

The current source already contains the actual standard-Gaussian measure and
Bochner moment layer, price duality and balancing, covariance pushforward,
facet flux, symmetric positive-semidefinite moment Laplacians, regular
tetrahedral attainment, radial comparison algebra, and conditional equality
reduction. `DiscreteMountainPass.lean` is unconditional finite-dimensional
ascent bookkeeping; it does not assume the Gaussian theorem.

Pinned toolchain: Lean 4.34.1 and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.
