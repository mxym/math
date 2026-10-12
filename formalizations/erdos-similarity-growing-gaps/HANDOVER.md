# Formalization handover (2026-10-11)

The working branch is `work`; the public branch is
`erdos-growing-gaps-formalization-20261010` in `mxym/math`. The latest pushed
commit is `718753d` (`Close finite sequence blocker assembly`). The pinned
toolchain is Lean 4.34.1 with Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

The deterministic and geometric parts are kernel closed. This includes late
annular/window extraction, exact input sequence identities, greedy annular
sampling, the explicit beta example, the finite Bernoulli routing law,
stable-center geometry and measure repair, the dyadic blocker, signed
countable exhaustion, tail distinctness, Theorem 2 for geometric tails, and
the Corollary 3/4 layers already present in `GeometricMain.lean`,
`CountableExhaustion.lean`, and `ExplicitExample.lean`.

The actual-sequence layer now has the following closed pieces:

- `SequenceGeometry.lean`, `SequenceRouting.lean`, and
  `SequenceRoutingProbability.lean` prove actual-log point identities,
  activation ranges, own/terminal address separation, and the fixed-parameter
  center-atom miss identity.
- `SequenceSignatures.lean` proves boundary-complete actual-log cuts,
  finite parameter representatives, and the continuum joint-miss estimate.
- `SequenceCounting.lean`, `SequenceGreedyRouting.lean`, and
  `SequenceGreedyFamily.lean` prove greedy prefix gap/separation bounds,
  child-wise active-cardinality bounds, a common prefix for all children of a
  vertex, and injectivity of the paired `(child,index)` list.
- `GlobalGreedyTests.lean` constructs the finite union of all local lists and
  proves local membership and its cardinality bound.
- `SequenceGreedyProbability.lean` proves the arbitrary finite-list missed
  center reduction, the center-atom probability bound, and the generic
  continuum estimate for such lists.
- `SequenceFiniteBlocker.lean` is the new finite actual-sequence assembly.
  `finite_sequence_routing_blocker` constructs an open one-periodic blocker
  with density `< 6p`, repairs arbitrary bounded tail errors, and returns
  `CompactRobustHits`. Its hypotheses are collected in
  `FiniteSequenceRoutingCertificate`; the global quantifier interface is
  `FiniteSequenceBlockerSpec`, and
  `compactRobustSpec_of_finiteSequenceBlockerSpec` is proved without an axiom.

`Replay.lean` contains 85 `#print axioms` roots. The latest aggregate build
completed 3436 jobs. The trust-zero replay reports only
`propext`, `Classical.choice`, and `Quot.sound`. No source uses `sorry`,
`admit`, `native_decide`, `unsafe`, `partial`, or a custom axiom.

The remaining theorem-level work is sharply localized. One must construct a
`FiniteSequenceBlockerSpec Z` from `WindowFilling Z`. Concretely, this means
choosing the variable branching/depth/gap/length tree on a late filled
annulus, proving its span fits the same origin, proving the finite greedy
prefix cardinality bound needed by the entropy estimate, and proving the
simultaneous tail-error inequality. The existing `VariableSchedule.lean`
contains the branching/depth little-o estimate; `ScheduledAnnulus.lean` and
`RoutingSchedule.lean` contain the origin scheduling interfaces. The missing
bridge is the joint asymptotic selection and its conversion into the fields
of `FiniteSequenceRoutingCertificate`. Until that bridge is closed, the
unrestricted `WindowFilling` version of Theorem 2 must not be declared a
complete Lean theorem.

Useful verification commands from this directory:

```sh
/workspace/tools/elan/bin/lake build ErdosSimilarityGrowingGaps.Replay
/workspace/tools/elan/bin/lake env lean -t 0 ErdosSimilarityGrowingGaps/Replay.lean
python3 checks/negative.py
```

The previous commits `b604eb3`, `f711c71`, and `f92b99b` contain the routing
sample-map, common greedy-family, and global-test-family milestones that lead
to `718753d`.
