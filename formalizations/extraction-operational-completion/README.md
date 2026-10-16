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

Compatibility of this same family with the sharp pure minimax profile remains
to be connected. Compilation alone is not an independent empty-kernel audit.
The `heterogeneous_projection_protocol` foundation constructs an actual common
unitary and complete local decoder for one large sector and many small sectors;
its input conditions are the original projection ranks and integer budgets.
`ppt_above_faithful_rate` and `ppt_above_eventualExact_rate` close the two
capacity converses, with their equality boundaries deliberately excluded.
No new publication or novelty claim is made by this package.
