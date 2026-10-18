# Actual APPT extraction-capacity applications

This separate package connects the compact set of actual APPT density matrices
on Fin m tensor Fin n to the genuine faithful-capacity supremum of achieved
rates in the extraction model. `physicalCapacity` uses actual finite adaptive
LOCC postprocessing, with the model's separately allowed global U. It agrees
with the full actual cPPT capacity on every density matrix.

`quantumEntropy A` is Re Tr(cfc Real.negMulLog A), including zero eigenvalues.
Its equality with the spectral Shannon entropy and continuity on Hermitian
matrices are proved through actual continuous functional calculus. Reindexing
is an explicit star-algebra equivalence, so the `flatten` coordinate bridge to
Fin(m*n) preserves density and spectral entropy. No entropy-continuity or
optimizer-attainment certificate is a premise.

`apptMinEntropy` is the real sInf of entropy values on the physical APPT set;
`apptMaxCapacity` is the real sSup of actual capacity values on that same set.
Both are attained by physical states. The entropy minimizer simultaneously
maximizes capacity and proves

    maxCapacity = min(log m, (log(m*n) - minEntropy)/2).

The collision-entropy inequality is proved for arbitrary nonnegative normalized
laws including zeros. It yields the actual pointwise capacity bound
C(A) <= log(m*n*purity(A))/2 and the APPT maximum bound using the existing
`APPTReview.apptPuritySup`, whose physical maximum attainment is retained.
This does not identify the APPT minimum-entropy optimizer or prove a global
closed entropy profile.

All old APPT/extraction audit scopes remain unchanged. Lean 4.34.1, Mathlib
pin d13f23b723b8a846827a245b89c10fc7d3f11612. Validation is ordinary compilation
only (BUILD_ONLY), pending independent audit. OperationalCompletion is compiled
independently in this worktree, while its frozen lower dependencies and Mathlib
reuse the D-backed shared builds. No full Mathlib copy is made.
