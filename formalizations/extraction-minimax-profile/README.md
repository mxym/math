# Actual minimax profile and universal extraction limits

This new, separate Lean 4.34.1 package defines a fixed protocol by an actual
original-space unitary and complete finite Kraus families for a trace-preserving
channel and its partial-transpose conjugate. Its minimax value is the supremum
of guarantees on the complete continuum of normalized pure iid inputs.

`MinimaxProfile.balanced_pure_target_uniform_minimax` proves, for each fixed
integer local dimension `m >= 2`, convergence to zero of the supremum over every
positive integer target dimension of the relative error from
`min(1, m^k / (K * sqrt(choose(k + m*m - 1, m*m - 1))))`.

The proof derives the actual pure-input support, its exact rank and adversarial
average from `extraction-symmetric-support`, and the physical all-channel
converse from `extraction-spectral-protocol`. It constructs an actual complete
local channel for the lower bound, retains both integer packing floors, and
proves that the maximum feasible integer packing has the required asymptotic.
Neither an average identity nor the desired rank/packing convergence is a
caller hypothesis of the final theorem.

The universal-compression modules construct one protocol before every unknown
density. `KrausPPTProtocol.IsProductLocal` explicitly retains two complete local
Kraus families and equality with their product channel after existential choice;
the only preceding joint operation is the original-space unitary. Integer
packing floors, an actual polynomial orbit space, and the empirical-entropy
word count are proved internally. Singular spectra are allowed.

`universal_subcritical_rate` proves unit-fidelity convergence below the entropy
threshold for an admissible integer target sequence. `universal_gaussian_limit`
proves the full Gaussian fidelity limit for the same density-independent family,
and the same `tensorInput` is used in the all-channel Gaussian and entropy strong
converses. Dimensions are fixed, convergence is pointwise in each fixed input,
Gaussian varentropy must be positive, and the target must remain at or below
both local dimensions. These local-cap hypotheses are essential at the boundary.
The tensor coordinates use a fixed dimension-preserving equivalence; they are
not asserted to be a literal copywise Alice/Bob coordinate formula.

The package compiles locally. The separate `extraction-connections` package
provides source-bound fresh rebuilding and trust-zero empty-kernel review of the
combined additions. Its generated `verification/LATEST.json` identifies an
actual completed audit; preparing a manifest alone is not verification.

This is not a proof of the whole submission. General-rank sharp Schur dimension
constants and Haar two-moment estimates, matching operational exponents and
reliability inverses, finite-block Berry--Esseen estimates, gate synthesis and
gate complexity, and a single family attaining both sharp pure minimax and all
mixed-state laws remain outside the current result.
Abstract completely positive maps are represented here by actual finite Kraus
families; equivalence with every alternative abstract channel presentation is
not asserted. Existing audited packages and their root scopes are unchanged.
