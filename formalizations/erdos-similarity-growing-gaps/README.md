# Lean formalization: Erdős similarity and growing logarithmic gaps

This package formalizes the deterministic sampling layer of the growing-gap
research note.  It is deliberately separate from the older globally bounded
log-gap formalization.

## Closed theorems

For a positive strictly increasing logarithmic scale `Z.z` tending to infinity,
`ConsecutiveLogGapLittleO Z` is the explicit epsilon formulation of

\[
z_{n+1}-z_n=o(\log\log z_n).
\]

The theorem
`ErdosSimilarityGrowingGaps.consecutiveGap_implies_annularFilling` proves
that this condition supplies arbitrarily late annuli in which every closed
interval of length `D` contains a sample, with `D >= 1` and
`D <= eta * log (log U)`.  The proof includes the first-sample endpoint case,
local gap propagation, and all positivity and logarithm estimates.

`AnnulusSequence.lean` upgrades the real annulus statement to the integer-origin
window sequence used in Definition 1, including the full `D / log(log U) → 0`
limit.  Thus the Lean bridge now reaches the paper's exact property `W`.

`Input.lean` closes the exact sequence interface: `a_n = 2^(-z_n)` is
positive, strictly decreasing, tends to zero, and satisfies
`-logb 2 a_n = z_n` in Lean.  These facts are not additional hypotheses.

`fillsAnnulus_of_anchor_gap` is the finite local lemma used by that theorem.
The package also replays the four variable-tree span/edge identities from the
research note in the `GrowingGap` namespace.

`FiniteRouting.lean` adds the finite Bernoulli-table normalization and the
exact all-miss identity for pairwise distinct terminal addresses.  These are
kernel-checked finite statements and do not use a numerical probability
checker.

`Avoidance.lean` adds the complete countable-exhaustion and topology layer.
Given a countable family of open periodic blockers with summable density
budgets, `closed_periodic_avoidance_of_blockers` constructs the closed periodic
complement, proves the strict measure estimate on every unit interval, proves
empty interior, and transfers infinitely many blocker hits to infinitely many
values outside the complement.  `replay_blocker_assembly` is the public
trust-level-zero replay root.

`TailAnalysis.lean` closes the tail-analysis part of the interface: power
controlled remainders converge to their center, a hit in every input tail
forces infinitely many distinct hit values without assuming injectivity, and
an error-exponent/constant grid reduces to arbitrary real `α` and `M`.
`WindowFilling.exists_late_annulus` extracts the exact late finite annulus
needed by each routing block.

`ParameterStrata.lean` gives a finite, boundary-complete representative set
for every affine-cut parameter rectangle, including exact zero strata.  Its
fully checked bound is the finite sign budget `3^m`; the sharper quadratic
arrangement bound used in the paper remains a separate optimization.

`exists_budget_allocation` and `blockerFamily_of_budgeted_blockers` make the
countable budget split explicit: any countable collection of already-built
open periodic blockers can be assembled under an arbitrary positive budget.

`Input.input_ratio_tendsto_zero` records the exact analytic implication that
logarithmic gaps tending to infinity force adjacent input ratios to tend to
zero; it is replayed independently of the blocker construction.

## Scope boundary

The finite blocker witness `BlockerFamily` is now an explicit, fully typed
interface.  Its existence from `WindowFilling` (the annular sampling to
continuum routing/projection argument) is still the remaining analytic
connection.  The package therefore does not silently claim an unconditional
Lean proof of Theorem 2 or of the displayed logarithmic-power example.  No
placeholder theorem is used for that connection: every declaration present is
kernel checked and the earlier deterministic theorems remain unchanged.
The exact interface and next obligations are recorded in
[`HANDOVER.md`](HANDOVER.md).

## Reproduction

Use Lean 4.34.1 and the pinned Mathlib revision in `lake-manifest.json`:

```sh
lake exe cache get
lake build ErdosSimilarityGrowingGaps
lake env lean -t 0 ErdosSimilarityGrowingGaps/Replay.lean
python3 checks/negative.py
```

The trust-level-zero replay reports only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`.  The negative check compiles a
 deliberately false stronger span bound and requires Lean to reject it.
