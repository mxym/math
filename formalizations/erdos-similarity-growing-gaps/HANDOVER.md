# Formalization handover (2026-10-10)

The current branch contains a large kernel-checked expansion of the growing-gap formalization.

The deterministic layer is complete: late annular/window extraction, exact input bounds, the sign-robust sampled-power error, and the tail distinctness argument all replay. The finite routing layer is also complete: finite table normalization and factorization, the actual selector/terminal address geometry, quadratic sign strata, entropy schedule, stable-center exceptional measure, measurable periodic repair, and the open compact dyadic blocker are proved in `RoutingLaw.lean`, `Routing*.lean`, `PeriodicRepair.lean`, `PowerCore.lean`, and `RoutingMain.lean`.

`CoefficientCover.lean` and `CountableExhaustion.lean` prove the signed dyadic/geometric countable budget construction. `GeometricMain.lean` therefore proves `MainTarget` for geometric tails. `ExplicitExample.lean` proves the requested (0<\beta<1) example (using the finite-prefix-safe (n+1) indexing), including the little-o gap estimate and adjacent ratio limit.

`WindowRepair.lean` now proves the actual sampled missed-center closedness/periodicity, uniform compact-exponent error budget, and arbitrary-remainder center repair. `Avoidance.lean` and `TailAnalysis.lean` are unconditional interfaces for arbitrary `WindowBlockerSpec`: they prove closed periodic complements, strict density on every unit interval, empty interior, and infinitely many distinct missed values. The remaining paper-level obligation is the uniform transfer from an arbitrary `WindowFilling Z` to the finite routing blocker, with a schedule whose origin is one of the supplied late annuli and with the sampler and error buffers tracked simultaneously. It remains a typed proposition; no axiom, `sorry`, or computational oracle is used.

`Replay.lean` has 26 public roots. Trust-zero output reports only `propext`, `Classical.choice`, and `Quot.sound`. `checks/negative.py` rejects the deliberately false span/probability controls.
