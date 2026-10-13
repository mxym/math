# Main theorem entry points — finite tree model

These entries are present in the 1,677-root audit of the 220-module proof package.
The mathematical source is fixed at `08602003af46b2a16aa33d7c7c429a197ab607d6`; the main integration preserves
all proof and scope input hashes. Each exact checkpoint has its own verification receipt.

**Read the actual hypotheses.** Full-response fiber counts require the full
distinct-positive-pole, positive-weight target class. The polynomial boundary
theorems cover all real rates without positivity. Controls in the steering and
energy results are signed; no general nonlinear-catchment or off-diagonal
measurement theorem is implied. Scope and exclusions are stated in
[GAPS.md](../../formalizations/hydrology-tree-core/GAPS.md).

| Exact Lean declaration | Scope |
| --- | --- |
| [`HydrologyTree.finite_graph_complete_all_leak_algebra`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/LocatedBoundarySingularSet.lean#L42) | Arbitrary leak, all real rates: independent graph presentation, formal Jacobian factorization and every exact coordinate power. |
| [`HydrologyTree.formalLocatedJacobian_exact_power`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/LocatedExactMultiplicities.lean#L37) | Exact coordinate multiplicity: the stated power divides and the next power does not. |
| [`HydrologyTree.locatedJacobian_zero_iff_all_rates`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/LocatedBoundarySingularSet.lean#L30) | Complete all-real zero-boundary criterion for the actual coefficient Jacobian. |
| [`HydrologyTree.catenary_standard_formal_polynomial`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/CatenaryFormalPolynomial.lean#L34) | Endpoint-path formal Jacobian monomial for every size and all rate values. |
| [`HydrologyTree.full_tree_resultant_jacobian`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/AllTreeResultant.lean#L91) | Exact signed root-leak characteristic/cofactor resultant versus actual Jacobian identity. |
| [`HydrologyTree.realResponseRecursiveEquiv`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/RealFiberClassification.lean#L45) | Complete recursive classification of unrestricted real realizations of a full positive Stieltjes target. |
| [`HydrologyTree.real_root_response_fiber_exact_card`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/RealFiberClassification.lean#L68) | Actual finiteness and exact factorial/hook count, not a count of candidates. |
| [`HydrologyTree.real_discharge_fiber_exact_card`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/DischargeFiber.lean#L106) | Exact count for co-located physical discharge, without a separately calibrated root leak. |
| [`HydrologyTree.finite_graph_all_real_leak_ODE_classification`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/RealLocatedODEClassification.lean#L90) | Independent finite graph, arbitrary leak: unrestricted real continuous-input ODE fiber classification. |
| [`HydrologyTree.real_unknown_leak_continuous_exact_card`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/RealLocatedODEClassification.lean#L76) | Exact unknown-leak-site continuous-history fiber count with actual site multiplicity. |
| [`HydrologyTree.real_full_response_trajectory_observable`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/TrajectoryObservability.lean#L78) | Actual trajectory observability within the explicitly quantified full-target and interval hypotheses. |
| [`HydrologyTree.real_full_response_controllable`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/PhysicalControllability.lean#L14) | Constructed continuous signed endpoint steering within the positive-horizon hypotheses. |
| [`HydrologyTree.real_full_response_minimum_energy_control`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/PhysicalMinimumEnergy.lean#L37) | Exact signed-control minimum energy and its equality condition on the stated time interval. |
| [`HydrologyTree.leak_location_all_input_indistinguishability`](https://github.com/mxym/math/blob/08602003af46b2a16aa33d7c7c429a197ab607d6/formalizations/hydrology-tree-core/HydrologyTree/LeakLocationIdentifiability.lean#L35) | Leak relocation preserves the specified collocated input/output experiments; off-diagonal observations are not asserted equivalent. |

The accompanying JSON binds each module to its SHA-256 and records the source
line. This index is navigation, not a substitute for a kernel proof or a new
certificate about altered source. The original complete verification artifacts
are preserved under `verification/hydrology-tree-core-<commit>/`.

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com; ORCID 0009-0000-3864-3536.
No external funding; AI-assisted research. Existing notices remain in force.
