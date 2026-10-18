# Operational completion (new extension scope)

This package extends the frozen 608-root extraction audit without modifying its
sources, roots or bound inputs. It uses Lean 4.34.1 and the same pinned Mathlib.

Current compiled endpoints construct one original-space unitary and two complete
local Kraus channels before quantifying over every unknown density matrix:

* `nested_universal_set_protocol` implements decreasing weights on actual
  orthogonal differences of nested universal orbit projections. Summation by
  parts transfers proved quantum cumulative-mass bounds to classical iid mass.
* `geometric_universal_protocol` constructs an explicit geometric packing grid.
  Integer rank/floor budgets follow internally from the empirical-type bound.
* `geometric_universal_prefix_protocol` shows that the same selected protocol
  retains every weighted entropy-prefix guarantee simultaneously.

Local complete product structure is retained as `IsProductLocal`. Tensor inputs
are exactly the matrices used in the frozen lower/converse API. No unknown
eigenbasis, auxiliary system, Schur decomposition, supplied mass assumption or
asymptotic endpoint is part of the construction hypotheses.

The explicit `gridProtocol` family is defined at all positive integer targets,
including targets above the local dimensions. Its proved asymptotic endpoints
include the subcritical rate, full entropy-limited Gaussian fidelity limit,
strict-direct error exponential upper bound and eventual exactly-one fidelity
below the rank threshold. Local sector feasibility follows from the rate gap.

`KrausPPTProtocol.tensor_error_tail` constructs the actual tensor-word subset
needed for a matching converse: its cardinality is bounded by the physical
quadratic budget, and its missing mass lower-bounds the actual protocol error.

`grid_reliability_limit` now proves the matching strict-direct reliability
exponent, and `optimal_reliability_limit` proves the same limit for the genuine
supremum of any actual PPT protocol sub-class containing the common local grid
family. The omitted mass and relative-entropy boundary approximation are proved
in the separate deviation-completion extension. All zero eigenvalues remain.

`gridProtocol_test_width` proves that the same selected protocol retains every
integer test width, and `lowEntropyMass_eventual_lower` supplies the associated
true iid change-of-measure lower bound.

`grid_fidelity_exponent` and `optimal_fidelity_exponent` now prove the full
matching fidelity exponent at every nonnegative rate, including arbitrary
subexponential rate-zero target sequences. `fidelityExponent_renyi` identifies
it with the manuscript's Renyi variational formula. The local cap is retained
inside the actual capped Holder bound and produces the additional above-cap
exponent. Singular and exactly flat full-rank inputs are included.

The `reservedProtocol` extension now combines the sharp balanced pure minimax
guarantee and the mixed-state laws in one fixed actual family. Compilation alone
is not an independent empty-kernel audit.
The `heterogeneous_projection_protocol` foundation constructs an actual common
unitary and complete local decoder for one large sector and many small sectors;
its input conditions are the original projection ranks and integer budgets.
`ppt_above_faithful_rate` and `ppt_above_eventualExact_rate` close the two
capacity converses, with their equality boundaries deliberately excluded.
No new publication or novelty claim is made by this package.

At the user-requested pause on 2026-10-16, `reservedProtocol_guarantees`
constructs one actual local protocol retaining both all finite mixed-state
entropy-prefix bounds and a large symmetric-sector pure-state packing bound.
The polynomial reservation asymptotics and the transfer of the full mixed-state
limit laws to this reserved family have not yet been proved. In particular,
this finite compatibility theorem is not a same-family sharp pure minimax limit.
The last ordinary aggregate build passed 4,063 jobs. This entire extension is
BUILD_ONLY: no new empty-kernel replay, forged-proof controls or independent CI
has been run for it. The frozen 608-root evidence applies to its original scope.

The historical pause status above is superseded by the 2026-10-18 extension:
`ReservationLimit` proves the logarithmic reservation losses negligible both
at first order and at the Gaussian scale, and the large-sector dimension ratio
tends to one. `balanced_reserved_family_sharp` proves the common family's sharp
pure guarantee uniformly in every positive integer target and the whole unknown
pure-input continuum for each fixed balanced local dimension. `ReservedLaws`
and its dependencies prove the same family's full nonnegative-rate fidelity
exponent, strict-direct reliability, Gaussian limit, subcritical rate and
eventually exact fidelity below the rank threshold. These declarations use
`reservedProtocol` itself; no separate existence witness is substituted for a
particular input or asymptotic regime. Equality boundaries retain the precise
restrictions of the individual declarations.

The subsequent compiled connections now include:

* `reservedFixedErrorTarget_gaussian`: the actual natural maximum target of the
  same family, with its fixed-error Gaussian inverse and eventual attainment.
* `reserved_optimal_gaussian_limit`: the actual real supremum over every physical
  protocol class containing the family, with the full Gaussian threshold.
* `CapacitySets`: faithful and eventual-exact capacities defined as suprema of
  actual attainable-rate sets. The zero-capacity boundary is included, using the
  exact one-dimensional target, and product LO/cPPT are instantiated directly.
* `finiteLOCC_capacities`: the same capacity formulas for genuinely adaptive
  finite-round local-instrument trees, through the separate LOCC interface.
* `ProbabilityEnsemble`: actual barycenters and physical average-state bounds for
  arbitrary measurable probability ensembles. Integrability follows from density
  compactness; no finite-support restriction remains.
* `ReservedTriangular`, `DimensionLoss`, `ShrinkingVariance`: finite Berry--Esseen
  bounds, genuine varying-dimension Gaussian approximation, an explicit total
  overhead at most `10 D^2 log(k+D)`, and the concrete sufficient condition
  `D^5 log^2(k+D)=o(k)` when `D V` is bounded below and `D T` is bounded above.
  Moment bounds are eventual; integer output-sector feasibility remains explicit.

This extension still remains BUILD_ONLY. The separate preliminary audit scaffold
does not constitute independent replay or CI evidence for these later endpoints.
The frozen manuscript and all older audit scopes remain unchanged.
