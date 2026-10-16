# Actual pure-input minimax profile

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

The package currently compiles locally. Its separate source-bound empty-kernel
review is being prepared. This is not yet a proof of the whole submission:
general-rank Schur dimension formulas and two-moment estimates, the complete
universal mixed-input protocol and its gate complexity remain separate work.
Abstract completely positive maps are represented here by actual finite Kraus
families; equivalence with every alternative abstract channel presentation is
not asserted. Existing audited packages and their root scopes are unchanged.
