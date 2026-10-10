# Formalization handover (2026-10-10)

The new kernel-checked material is concentrated in two modules.

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

`Replay.lean` replays nine public roots at trust level zero.  The recorded
axioms are only `propext`, `Classical.choice`, and `Quot.sound`; the source
contains no `sorry`, `admit`, custom axiom, `unsafe`, `partial`, or
`native_decide`.  `checks/negative.py` rejects both a false tree inequality
and a false finite probability equality.

The exact remaining proof obligation is the construction of a
`BlockerFamily` (equivalently `WindowBlockerSpec`) from `WindowFilling`.  This
is the continuum routing/projection argument: finite parameter rectangles,
stable-center exceptional sets, the error buffer, and the late-window
schedule must still be connected to the new finite and topological layers.
The repository deliberately leaves this as a typed proposition rather than
introducing an axiom or an unproved theorem.  The unconditional Theorem 2
and the explicit `n(log log(n+20))^β` example therefore remain written
claims in the preprint.

## Verification record

The pinned Lean 4.34.1 compiler directly compiled every owned module and the
aggregate import.  Trust-level-zero replay and both negative controls passed;
`results/reproduce.log`, `audit.json`, and `SHA256SUMS` record the run.
