# Formalization handover (2026-10-10)

The new kernel-checked material is concentrated in three modules.

* `FiniteRouting.lean` proves Bernoulli weight normalization, nonnegativity,
  coordinate factorization at distinct addresses, and the exact terminal
  all-miss probability `(1-p)^m`.
* `Avoidance.lean` defines `TailApproximation`, `RobustBlocker`, and
  `BlockerFamily`, then proves the full countable union/topological assembly.
  From a summable family of open periodic blockers it constructs the closed
  periodic complement, proves the strict Lebesgue estimate on every shifted
  unit interval, proves empty interior, and transfers infinite blocker hits
  to infinite outside values.  The compact `[0,1]` restriction and the
  `WindowBlockerSpec` bridge are also closed.
* `TailAnalysis.lean` proves convergence of every power-controlled tail,
  eventual exclusion of the leading center, and the key fact that one hit in
  every input tail yields infinitely many distinct hit values.  It also proves
  the countable grid reduction from `α = 1/(j+1)` and integer error budgets to
  arbitrary real `α` and `M`.
* `WindowFilling.exists_late_annulus` turns the sequential late-window
  hypothesis into the exact finite annulus witness used by a routing block.
* `ParameterStrata.lean` constructs representatives for every finite affine
  cut rectangle, retaining negative, zero, and positive boundary strata with
  a checked `3^m` bound.  This is the finite parameter cover; the paper's
  sharper quadratic refinement is still needed for the final entropy budget.
* `exists_budget_allocation` and `blockerFamily_of_budgeted_blockers` close
  the countable budget bookkeeping once the individual open blockers exist.

`Replay.lean` replays thirteen public roots at trust level zero.  The recorded
axioms are only `propext`, `Classical.choice`, and `Quot.sound`; the source
contains no `sorry`, `admit`, custom axiom, `unsafe`, `partial`, or
`native_decide`.  `checks/negative.py` rejects both a false tree inequality
and a false finite probability equality.

The exact remaining proof obligation is the construction of a
`BlockerFamily` (equivalently `WindowBlockerSpec`) from `WindowFilling`.  The tail and countable-grid bookkeeping is now closed; the remaining
continuum routing/projection argument is the actual random finite-table
construction, stable-center exceptional sets, parameter-sign strata, error
buffer, and late-window schedule connected to one measurable open blocker.
The repository deliberately leaves this as a typed proposition rather than
introducing an axiom or an unproved theorem.  The unconditional Theorem 2
and the explicit `n(log log(n+20))^β` example therefore remain written
claims in the preprint.

## Verification record

The pinned Lean 4.34.1 compiler directly compiled every owned module and the
aggregate import.  Trust-level-zero replay and both negative controls passed;
`results/reproduce.log`, `audit.json`, and `SHA256SUMS` record the run.
