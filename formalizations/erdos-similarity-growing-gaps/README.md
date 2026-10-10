# Lean formalization: Erdős similarity and growing logarithmic gaps

This package contains the kernel-checked deterministic and finite-routing layers for the growing-logarithmic-gap preprint. It keeps the unconditional statements separate from the remaining transfer from the paper's late-window hypothesis to a finite routing schedule.

## Closed Lean results

- `consecutiveGap_implies_annularFilling` and `consecutiveGap_implies_windowFilling` prove the exact late-window property from the stated epsilon formulation of `z_{n+1}-z_n=o(log log z_n)`, including endpoint sampling.
- `Input.lean` proves positivity, strict decrease, convergence to zero, the base-2 logarithm identity, and the ratio limit from diverging gaps.
- `FiniteRouting.lean`, `RoutingLaw.lean`, `RoutingProbabilityFinite.lean`, and the routing geometry modules prove the finite Bernoulli law, distinct-address factorization, boundary-complete parameter arrangements, stable-center measure budget, and the finite schedule bounds.
- `PeriodicRepair.lean` and `RoutingMain.lean` construct an open one-periodic compact dyadic power blocker with the stated density bound and repair all centers using the infinite tail.
- `CoefficientCover.lean`, `CountableExhaustion.lean`, and `GeometricMain.lean` close the signed dyadic/geometric countable exhaustion and its compact positive-measure target. This is a genuine unconditional theorem for geometric tails.
- `Avoidance.lean` and `TailAnalysis.lean` prove the countable budget union, closed periodic complement, unit-interval measure estimate, empty interior, and infinitely many distinct outside values once the per-grid blockers are supplied. `WindowRepair.lean` adds the actual `LogScale` missed-center relation, its closedness/periodicity, a uniform tail error budget, and the arbitrary-remainder center repair theorem.
- `ExplicitExample.lean` proves, for `0 < β < 1`, the shifted positive representative `z_n = (n+1)(log log(n+20))^β`, the strict increase, divergence, and `z_{n+1}-z_n=o(log log z_n)`, together with the adjacent input ratio limit. The shift only removes the zero value at index zero and is a finite-prefix reindexing of the displayed example.

All these results compile with Lean 4.34.1 and the pinned Mathlib revision. `Replay.lean` exposes 26 trust-level-zero roots; their only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## Current theorem boundary

The finite routing/blocker construction is now closed for the exact dyadic power rectangle, and the complete geometric-tail target is closed. The remaining connection for the full preprint theorem is the uniform late-window transfer: choose a routing template on an annulus supplied by `WindowFilling`, absorb the sampled exponent and tail remainder into the open buffers, and then instantiate the countable `(s, α, M, c)` grid. This interface is represented by `WindowBlockerSpec`; it is not replaced by an axiom or a placeholder theorem. Consequently the unrestricted `WindowFilling` version of Theorem 2 remains a written theorem until that transfer is added.

## Reproduction

```sh
LAKE_BIN=/workspace/tools/elan/bin/lake python3 reproduce.py
```

The script builds `ErdosSimilarityGrowingGaps`, runs `Replay.lean` with `-t 0`, and executes `checks/negative.py`. No source uses `sorry`, `admit`, a custom axiom, `native_decide`, `unsafe`, or `partial`.
