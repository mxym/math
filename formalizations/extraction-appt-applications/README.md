# Actual APPT extraction-capacity applications

This separate package connects the compact set of actual APPT density matrices
on Fin m tensor Fin n to the genuine faithful-capacity supremum of achieved
rates in the extraction model. `physicalCapacity` uses actual finite adaptive
LOCC postprocessing, with the model's separately allowed global U. It agrees
with both closure-LOCC and full actual cPPT capacity on every density matrix.

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

The explicit state `spikeState m n v = (I+2 vv*)/(D+2)` is proved density/APPT
for every unit vector, deriving the uniform pure partial-transpose lower bound
from the existing actual Schmidt decomposition. CFC interpolation on the actual
rank-one projection proves its entropy and, for all 2 <= m <= n, its exact
faithful capacity

    C = (log(D/(D+2)) + 3 log(3)/(D+2))/2.

With c=(3 log(3)-2)/2, the internally proved finite remainder is

    0 <= c/D - C <= 3 log(3)/(D(D+2)).

Thus the actual spike-state capacity has leading coefficient c along arbitrary
growing product dimensions and arbitrary unit vectors. In square systems the
existing attained physical APPT purity-eight law gives an explicit upper budget
whose product with D converges to 4. `balanced_apptMaxCapacity_upper_remainder`
provides Cmax <= 4/D + e(k)/D with e(k)->0. The final actual-max comparison
retains any square dimension sequence m(k)->infinity and proves, eventually
for every epsilon>0,

    c-epsilon <= D*Cmax <= 4+epsilon.

These are bounds on the true attained APPT maximum. They do not assert that
the maximum's leading coefficient or its entropy optimizer has been solved.

All old APPT/extraction audit scopes remain unchanged. Lean 4.34.1, Mathlib
pin d13f23b723b8a846827a245b89c10fc7d3f11612. Validation is ordinary compilation
only (BUILD_ONLY), pending independent audit. OperationalCompletion is compiled
independently in this worktree, while its frozen lower dependencies and Mathlib
reuse the D-backed shared builds. No full Mathlib copy is made.
