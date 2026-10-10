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

## Scope boundary

This package does **not** claim a Lean proof of the full positive-measure
avoidance theorem.  The random routing, continuum parameter stratification,
measure construction, countable exhaustion, and nowhere-dense endpoint remain
to be formalized.  The existing written proof and the earlier globally bounded
log-gap formalization are not silently substituted for those missing modules.

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
