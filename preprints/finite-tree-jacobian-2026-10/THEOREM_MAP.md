# Finite-tree paper: theorem, lemma and Lean correspondence

Prepared 2026-10-14. This map is established before the manuscript. It describes
the existing proof package; it introduces no Lean theorem or audit root.

The proof source is `c2a2ce36ea6c5e000225574835f5a3ceddc748b4`, with 235 proof,
reproduction and public-scope inputs. The original independent run is
[38383557356](https://github.com/mxym/math/actions/runs/38383557356). A new
source/archive/API readback is in `verification/research-resume-20261014/`.
This readback is not a new fresh build or kernel replay.

| Manuscript statement | Necessary ingredients | Exact existing Lean declarations / modules |
| --- | --- | --- |
| Theorem 1: all-real arbitrary-leak coefficient Jacobian | Actual graph matrix and original principal cofactors; root branch gluing; relocation derivative; polynomial extension | `finite_graph_complete_all_leak_algebra`, `formalLocatedJacobian_coordinate_factorization`, `formalLocatedJacobian_evaluate`; LocatedBoundarySingularSet, LocatedExactMultiplicities, LocatedPolynomialWeight |
| Lemma 3: coefficient gluing has squared sibling resultants | Product derivative is the polynomial numerator assembly; determinant of that linear map is the pairwise resultant product | `familyProductDerivative_polynomial`, `familyProductJacobian_eq_pairwise`, `familyGlueJacobian_eq_pairwise`; FamilyGluing, FamilyResultants |
| Root-leak specialization | Rate chart determinant; monic child cofactor scaling; induction on actual child matrices | `det_rateChartDerivative`, `treeCanonicalJacobian_recurrence`, `all_tree_canonical_jacobian`; RateChart, TreeJacobianRecurrence, AllTreeJacobian |
| Relocation and all-real extension | Actual diagonal similarity on each principal block; slide differential; cofactor-at-zero conservation identity; infinite-box polynomial equality | `slideLeakJacobian_formula`, `leakWalkJacobian_leak_weight`, `locatedGraphJacobian_leak_weight`, `graphCharacteristic_eval_zero_leak`, `locatedGraphJacobian_all_real_factored`; LeakSlideJacobian, LocatedLeakJacobian, GraphLeakCofactor, LocatedAllRateJacobian |
| Theorem 1: exact coordinate powers and full zero set | Signed triangular witnesses on every original coordinate hyperplane; residual nondivisibility; coordinate-variable multiplicity | `symbolicLocatedResidual_no_coordinate_factor`, `formalLocatedJacobian_exact_power`, `locatedJacobian_zero_iff_all_rates`; GraphResidualWitness, LocatedExactMultiplicities, LocatedBoundarySingularSet |
| Corollary 2: endpoint-path monomial and root-tree exponents | Actual path specialization; inward/outward subtree exponents; coefficient order permutation | `catenary_standard_formal_polynomial`, `located_collocated_inward_multiplicity`, `located_collocated_outward_multiplicity`; CatenaryFormalPolynomial, LocatedExactMultiplicities |
| Theorem 4: exhaustive root-leak real response fibers | Full Stieltjes reciprocal, labelled allocations, reconstruction, reverse extraction, response-to-coefficient uniqueness | `stieltjes_reciprocal_polynomial`, `real_stieltjes_realization_is_positive`, `realResponseRecursiveEquiv`, `real_root_response_fiber_exact_card`; StieltjesReciprocal, RealFiberRigidity, RealFiberClassification |
| Theorem 4: all-real fibers at any fixed leak site | Supported-tree diagonal gauge construction; same-site conservative gauge rigidity; positive relocation equivalence | `supported_positive_diagonal_realization`, `graph_same_leak_gauge_unique`, `real_located_response_forces_positive`, `realLocatedRecursiveEquiv`, `real_located_fiber_exact_card`, `real_located_full_response_positive_regular`; SupportedPositiveGauge, ConservationGaugeRigidity, RealLocatedPositivity, RealLocatedClassification |
| Theorem 4: unknown-site multiplicity is an actual matrix count | Site and rate injectivity of the physical matrix; leak is strictly positive | `real_unknown_leak_fiber_exact_card`; RealLocatedClassification, GraphModelInjectivity, LeakLocationIdentifiability |
| Proposition 5: continuous-input histories | Actual global linear ODE solutions; exponential probing before positivity; both transfer/history implications | `real_located_continuous_iff_response`, `finite_graph_all_real_leak_ODE_classification`; RealLocatedODEClassification, MatrixTimeIdentification, LocatedLeakDynamics |

Precise types and their hypotheses must be read in the named source modules.
The existing [entrypoint index](../../research/hydrology-tree-real-fibers/THEOREM_ENTRYPOINTS.md)
binds its declarations to module SHA-256 and source lines. Full-target fiber
theorems require N distinct positive poles, positive weights summing to one,
and a fixed finite labelled tree with collocated input and state observation.
All-real Jacobian and multiplicity theorems impose no positivity hypothesis.
The minimum-energy and signed-control roots already in the package are not
additional main claims of this focused manuscript. No fewer-mode, complex-rate,
multiple-leak, cycle, off-diagonal output, or nonlinear hydrology theorem is added.

An independent assistant review of the manuscript will be recorded separately.
It is not external human peer review and does not establish historical priority.
