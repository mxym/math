# Affine geometric avoidance theorem and module map

## How to read this map

The completed result is `ContinuumGeometric.geometric_main_target : ContinuumGeometric.MainTarget`, in [ContinuumGeometric/MainProof.lean](ContinuumGeometric/MainProof.lean). Its definition is in [ContinuumGeometric/Target.lean](ContinuumGeometric/Target.lean). The [proof roadmap](PROOF_ROADMAP.md) explains the mathematics and all parameter choices.

Every filename here is relative to the Lean project root, `formalizations/geometric-avoidance/` in the public repository. All declarations listed below have prefix `ContinuumGeometric.`. A name beginning `RoutingTemplate.` has the full prefix `ContinuumGeometric.RoutingTemplate.`. These are exact declaration names; the filename alone does not add another namespace.

This is a reading map of all 45 specification and implementation modules, with selected definitions and theorems. It is not a replacement for the full declaration dependency graph. In particular, an import is not evidence that every declaration in the imported module occurs in the final proof. Two supporting modules with no declaration in the audited final proof closure are identified explicitly below.

## The exact public theorem

For every ε ∈ ℝ with 0 < ε < 1, there exists one compact E ⊆ [0,1] with Lebesgue measure λ(E) > 1 − ε, such that

for all a,b,q ∈ ℝ, if a ≠ 0 and 0 < q < 1, then for every N ∈ ℕ there exists n ∈ ℕ with N ≤ n and a qⁿ + b ∉ E.

The same E serves all real parameters and all tails. The measure in the Lean statement is `MeasureTheory.volume` on ℝ, and its lower bound is `ENNReal.ofReal (1 - ε)`. No parameter is assumed rational or sampled, and no exceptional set of centers is permitted in the conclusion. The cases a = 0, q = 0, and q = 1 are deliberately excluded; each allows a constant tail in a nonempty E.

The stronger continuum-profile theorem with a nonlinear remainder remains written-only and is outside this result. The completed affine-geometric theorem has no such remainder and no unresolved construction hypothesis.

## The shortest route through the final proof

1. `exists_routing_schedule`, in `ContinuumGeometric/RoutingSchedule.lean`, constructs the actual finite tree parameters and every required strict numerical budget.
2. `actual_stable_missed_center_probability_le`, in `ContinuumGeometric/RoutingStableProbability.lean`, proves the actual global missed-center probability is at most 2p at every stable real center.
3. `actual_routing_blocker_of_actual_stable_miss`, in `ContinuumGeometric/RoutingAssembly.lean`, combines that estimate with measured instability, finite weighted averaging, open buffers, and closed-set repair to construct a blocker with density less than 6p.
4. `smallCompactBlockerSpec_proved`, in `ContinuumGeometric/MainProof.lean`, takes p = δ/12 and proves `SmallCompactBlockerSpec` itself.
5. `smallCompactBlockerSpec_open_exhaustion`, in `ContinuumGeometric/CountableExhaustion.lean`, covers all compact exponent ranges, integer scales, signs, and original tails with one open periodic set U of density less than ε.
6. `compact_complement_of_open_small`, in the same module, makes E = [0,1] ∖ U compact and preserves the strict volume inequality.
7. `mainTarget_of_smallCompactBlockerSpec` is the conditional bridge. `geometric_main_target` applies it to the proved specification, so the final theorem is unconditional.

## Definitions parameterization and index bounds

### ContinuumGeometric/Target.lean

- `AvoidsGeometricTails` defines the complete ∀a ∀b ∀q ∀N ∃n statement.
- `MainTarget` places ∃E before those universal quantifiers and includes compactness, containment, and the strict actual-volume inequality.

These are proposition definitions. The proof is supplied by `MainProof.lean`; a historical `UNRESOLVED` comment in the preserved definition is not the final theorem's status.

### ContinuumGeometric/GeometricParameters.lean

- `dyadic` is the exact sequence n ↦ (1/2)ⁿ.
- `dyadic_power_eq` proves ((1/2)ⁿ)ˢ = ((1/2)ˢ)ⁿ for every natural n.
- `geometric_parameter` represents every real q ∈ (0,1) by a positive real exponent s.
- `affine_geometric_tendsto` and `every_tail_hits_open` prove convergence to the center and arbitrarily late hits in an open neighborhood of that center.

This module supplies both the ratio cover and the convergence needed for repair.

### ContinuumGeometric/GeometryChain.lean

- `exists_compact_exponent_range` puts any s > 0 in [1/K,K] for some natural K ≥ 2. This is the part used by the final coefficient cover.
- `exists_spaced_sampling`, `sampled_output_gap`, and `complete_geometric_activation_chain` are supporting assembly results for exponent sampling and activation.

Only compact ranges are countably exhausted; the exponents within each range remain real and unrestricted.

### ContinuumGeometric/Activation.lean

- `activeIntegers`, `activeNaturals`, and `mem_activeIntegers_iff` encode strict activation without admitting either boundary.
- `activation_card_exact` gives the ceiling-minus-floor-minus-one count.
- `activation_card_lower` and `activation_card_uniform` give the linear-in-window-length lower bound.
- `activation_tail`, `activeNaturals_card`, and `mem_activeNaturals_iff` justify passage to natural indices.
- `compact_power_activation` is a supporting uniform formulation.

### ContinuumGeometric/ShiftedActivation.lean

- `compact_shifted_original_activation` states the shifted count with original indices m·n and the signed coefficient shift k.

This is an imported supporting helper. It has no declaration in the audited stored proof closure of `geometric_main_target`; the final candidate construction proves the needed original-index facts in `CandidateBounds.lean`. Its presence must not be mistaken for an extra hypothesis or a missing dependency.

### ContinuumGeometric/CandidateBounds.lean

- `candidateStride` and `candidateStride_gap` choose m = ⌈3/s₀⌉ + 2 and prove m s₀ > 3.
- `candidateLabelBudget` retains ⌈(U + T + |k|)/3⌉ + 1.
- `candidateOriginalIndices`, `active_original_index_tail`, and `active_original_index_mem_candidates` keep original indices and the original tail N.
- `activeOriginalIndices_count_bounds` gives the active count at every real parameter.
- `potentialOriginalPairs`, `mem_potentialOriginalPairs_exact`, and `potentialOriginalPairs_card_le` give the finite family of all potentially active edge/index pairs and its size bound.
- `candidatePairEnumeration_complete` and `candidatePairEnumeration_injective` justify its indexed enumeration.
- `activeOriginalPairs_eq_potential_filter` and `potentialOriginalPairs_active_count` connect that enumeration to the actual active tests.
- `candidateTailStart_guards` supplies both U ≥ 4 and the signed tail-start inequality; `original_activation_endpoints_inactive` records the boundary convention.

### ContinuumGeometric/CoefficientCover.lean

- `positive_dyadic_coefficient_cover` gives a = t2ᵏ with k ∈ ℤ and 1 ≤ t < 2 for a > 0.
- `signed_dyadic_coefficient_cover` adds the coefficient sign.
- `affine_geometric_compact_power_cover` gives the exact identity for every original n, using center b in the positive branch and reflected center −b in the negative branch.

## Boundary complete continuum signatures

### ContinuumGeometric/Interfaces.lean

- `CutSign`, `cutSign`, `AffineCut`, `evalCut`, and `inRectangle` define three-sign affine arrangements.
- `ArrangementRepresentativeBound` is the proposition specifying finite representatives with bound 20(m + 5)² on a closed rectangle.

The proposition is proved by `arrangementRepresentativeBound` in `Planar.lean`; it is not an assumed axiom. Coincident, parallel, constant, and identically zero cuts are permitted.

### ContinuumGeometric/LineSignBound.lean

- `rootCode` distinguishes intervals between roots from the roots themselves.
- `affine_sign_equal_of_rootCode` and `line_signs_equal_of_rootCode` show that the code preserves exact signs.
- `realizedLinePatterns_card_le` bounds the sign patterns of n affine functions on a line by 2n + 1.

### ContinuumGeometric/SignFiberCount.lean

- `oldPatterns` and `zeroPatterns` distinguish existing sign patterns from those realized on the new cut's zero set.
- `card_le_oldPatterns_add_two_zeroPatterns` bounds the increase in patterns when a new cut is added.

The crossing condition is proved geometrically in `Planar.lean`, rather than imposed on an unexplained arrangement.

### ContinuumGeometric/Planar.lean

- `plane_zero_between` and `realizedPairs_cross` use line segments to connect opposite signs within an old sign pattern.
- `zeroPatterns_card_le` applies the one-dimensional bound on a nonconstant cut's zero line.
- `realizedPlanePatterns_card_le` proves the bound 2m² + 1 with all three signs.
- `arrangementRepresentativeBound` selects representatives inside the closed rectangle and supplies the stated 20(m + 5)² interface bound.

The theorem preserves lower-dimensional and boundary strata, not just open two-dimensional cells.

### ContinuumGeometric/GridCutBridge.lean

- `gridCrossingCut` and `logPowerParams` move exact positive offset comparisons into the affine coordinates (s, log t).
- `power_grid_cut_sign` and `actual_grid_boundary_sign` prove equality of negative, zero, and positive signs before and after taking logarithms.
- `activation_cut_signs` handles both strict activation endpoints.
- `power_parameter_sign_representatives` pulls rectangle representatives back to the original power parameters.
- `signature_representatives_uniform_readout` is a general signature-readout interface. The actual routing factorization is supplied later.

### ContinuumGeometric/BoundedGrid.lean

- `periodicGridKey` is ⌊Nz⌋ mod N, defined for real z.
- `cutSign_pos_mul` and `grid_boundary_sign_rescale` preserve the signs when the grid comparison is rescaled.
- `bounded_floor_eq_of_boundary_signs` and `bounded_periodicGridKey_eq` are supporting finite-boundary key lemmas.

The actual local boundary selection used in the final continuum argument is in `LocalSignatures.lean`.

### ContinuumGeometric/LocalSignatures.lean

- `dyadic_shifted_offset` proves the exact shifted-power identity.
- `active_power_point_range` bounds every active point relative to its real center.
- `liftedBoundaryBatch` and `liftedBoundaryBatch_card_le` select only relevant positive lifted boundaries and bound their number uniformly in the center.
- `localGridVector` retains both activation and key: inactive tests are `none`, active tests are `some(key)`.
- `actual_local_grid_representatives` gives exact vector representatives.
- `dyadic_boundary_batch_card_le` and `localParameterCuts_card_le_span` use the actual local span to bound the cut count.
- `actual_local_representatives_entropy_bound` gives 20[P(3 + 2^(2ℓ+3)) + 5]².

The additive constant remains present when P = 0.

## The finite routing construction and its deterministic geometry

### ContinuumGeometric/RoutingInterfaces.lean

- `OnePeriodic` and `unitDensity` define periodicity and actual Lebesgue measure on [0,1).
- `CompactPowerHits` quantifies over all real centers and the whole compact power rectangle.
- `SmallCompactBlockerSpec` is the precise intermediate existence statement for every K ≥ 2, integer k, original tail N, and 0 < δ < 1.
- `FiniteRoutingTables`, `centerExposureAtom`, `localRoutingSuccess`, `localRoutingAllMiss`, and `LocalAddressSeparation` define the finite table model and its separation contract.
- `periodicGridSet` is a set determined by actual modulo-floor keys.

The probability and construction obligations expressed here are discharged in later modules and `MainProof.lean`.

### ContinuumGeometric/RoutingTemplate.lean

- `InternalNode`, `RoutingEdge`, `SelectorEdge`, and `RoutingLeaf` are concrete complete-tree path types.
- `RoutingTemplate` stores gap, base length, and origin.
- `RoutingTemplate.span`, `RoutingTemplate.lengthAt`, `RoutingTemplate.blockSpan`, `RoutingTemplate.edgeStart`, `RoutingTemplate.edgeEnd`, and `RoutingTemplate.edgeStar` define the recursive preorder layout, including default edges.
- `RoutingTemplate.edge_span_bound` bounds an edge-plus-subtree block by twice the edge length.
- `RoutingTemplate.span_affine` proves the exact dependence A·L + B·g.
- `SelectorAddress` and `TerminalAddress` are finite tagged address types with the prescribed dyadic grid sizes.

### ContinuumGeometric/RoutingGeometry.lean

- `gridAddress`, `selectorAddress`, and `terminalAddress` turn periodic keys into finite addresses.
- `periodicGridKey_fract` accounts for negative centers and integer wrap.
- `periodicGridKey_refinement` and `dyadic_grid_eq_of_finer_eq` give exact refinement, including equality at grid boundaries.
- `NoGridBoundary` and `periodicGridKey_eq_of_no_boundary` formalize preservation on a stable predecessor interval.
- `periodicGridKey_ne_of_scaled_gap` proves distinctness modulo the period from a quantitative displacement bound.
- `actualCenterExposure`, `centerExposure_reads`, and `own_selector_unexposed` describe the center exposure and unexposed own reads.

### ContinuumGeometric/RoutingModel.lean

- `chooseRoutingChild` selects the first true nondefault child or the last, default child.
- `chooseRoutingChild_of_first_true`, `chooseRoutingChild_of_all_false`, and `chooseRoutingChild_eq_of_reads_before_choice` prove its read behavior.
- `routeFromList`, `routeLeaf`, `localRouteLeaf`, and `localTerminalAddress` give the global and forced-entry local routes.
- `routedSet` is the actual final terminal-bit readout.
- `routeHasNoDefault` records the relevant center-route event.
- `center_atom_routeLeaf_eq` and `center_atom_noDefault_iff` show that an exposure atom fixes the route.

### ContinuumGeometric/RoutingProbability.lean

- `routeLeaf_eq_iff_prefix_choices` characterizes the actual routed leaf by its successive choices.
- `routeLeafFrom_eq_of_actual_prefix`, `routeLeaf_prefix_of_prefix_choices`, and `routeLeaf_eq_routeLeafFrom_of_prefix_choices` connect full routes with routes started at prefixes.

Despite its filename, these are deterministic routing facts. They support both the local-to-global connection and the later probability calculation.

### ContinuumGeometric/RoutingTreeBounds.lean

- `RoutingTemplate.edgeStart_ge_origin` and `RoutingTemplate.edgeEnd_within_total` bound actual window positions.
- `RoutingTemplate.descendant_incomingEnd_bounds` handles full descendant subtrees.
- `localRouteLeaf_grid_bounds` bounds the terminal endpoint of every possible local route between its incoming edge endpoint and subtree endpoint.
- `descendant_selectorEnd_le_star` bounds every selector read in a child subtree by its local finest endpoint.
- `selectorEnd_global_bound` and `leafEnd_global_bound` give the common finest global endpoint.

### ContinuumGeometric/RoutingPreorder.lean

- `preorderActualWindows_eq_schedule` proves that recursive placement agrees with a sequential preorder schedule over all edges.
- `preorderPaths_nodup` and `routingEdge_mem_preorderPaths` ensure that actual edges are represented correctly.
- `RoutingTemplate.earlier_edgeEnd_add_gap_le` controls any earlier edge.
- `RoutingTemplate.predecessorBoundary` is the concrete endpoint u − g − 1.
- `RoutingTemplate.predecessorBoundary_start` uses the origin guard to prevent natural subtraction truncation.
- `RoutingTemplate.earlier_edgeEnd_le_predecessorBoundary` connects ordering to every earlier grid.

### ContinuumGeometric/RoutingActiveGeometry.lean

- `active_power_offset_lower` supplies the lower displacement from the strict upper activation bound.
- `active_window_grid_scale` computes the four-cell lower scale; `active_power_point_short` bounds offsets by 1/8.
- `active_power_gridAddress_ne_center` separates an own read from its center read.
- `power_point_offset_ratio_of_output_gap`, `active_power_point_gap_lower`, and `active_subsequence_gridAddress_ne` give stride-based pairwise separation, including the 28-cell lower gap.
- `active_original_gridAddress_injective` keeps the original-index interface.
- `active_power_coarser_preceding_gridAddress_eq` propagates stable predecessor equality to every earlier grid.

### ContinuumGeometric/RoutingSeparation.lean

- `actual_local_address_separation` proves the full `LocalAddressSeparation` contract from own-grid geometry.
- `active_original_local_address_separation` discharges that geometry for actual strict-active original stride indices.

Terminal injectivity holds for every selector assignment, even when local paths share auxiliary reads or own bits are false. Different table tags and finer terminal grids are part of the proof.

### ContinuumGeometric/RoutingLocalHit.lean

- `ancestor_selector_precedes` and `point_followsNodePrefix_of_earlier_keys` show that earlier-key agreement preserves the necessary ancestor decisions.
- `routeLeaf_eq_localRouteLeaf_of_prefix_and_success` connects forced local entry to the actual global route.
- `actual_local_success_mem_routedSet` turns local selector-and-terminal success at a center-default vertex into actual set membership.

### ContinuumGeometric/RoutingStableMeasure.lean

- `gridBoundaryBad`, `gridBoundaryStable`, and `gridBoundaryCore` encode the half-open boundary strips.
- `gridBoundaryBad_eq_integerPeriodization` includes negative lifts and periodic wrap.
- `unitDensity_gridBoundaryBad_le` proves the upper bound G·R without assuming strips are disjoint.
- `dyadic_gridBoundary_cost` gives the cancellation to 2^(3−g).
- `unitDensity_routingStable_compl_le` sums the cost over the finite edge family.

### ContinuumGeometric/RoutingStableGeometry.lean

- `actualStableCenters` uses the actual predecessor vector from the complete preorder.
- `measurableSet_actualStableCenters` and `unitDensity_actualStable_compl_le` supply the measurable exceptional set and its density bound.
- `actual_stable_earlier_address_agreement` proves preservation of every earlier selector key at every active point.
- `actual_stable_local_success_mem_routedSet` supplies the full deterministic implication used by global failure estimates.

### ContinuumGeometric/RoutingFactorization.lean

- `localRouteLeaf_eq_of_finest_key`, `localTerminalAddress_eq_of_finest_key`, and `localOwnAddress_eq_of_finest_key` prove that local finest keys control all actual reads.
- `actualLocalAllMiss_iff_of_localGridVector_eq` retains activation as well as addresses.
- `actual_routing_local_representatives` connects the quadratic signature bound to the actual routing all-miss event, uniformly for every complete table assignment.

The representative choice precedes the outcome quantifier. This is the bridge from continuum arrangement geometry to the finite probabilistic union bound.

### ContinuumGeometric/RoutingGlobalGrid.lean

- `actual_routing_readout_eq_of_finest_key` proves that the global readout factors through the common finest key.
- `routedCanonicalCells` and `routedCanonicalCells_subset` give an actual canonical finite cell family.
- `actual_routedSet_finite_grid` identifies the routed set with that periodic grid set at endpoint U + T − 1.
- `measurableSet_actual_routedSet_of_template` and `onePeriodic_actual_routedSet_of_template` give the properties used by the measure assembly.

## Finite probability scheduling and stable global failure

### ContinuumGeometric/FiniteRoutingProbability.lean

- `bernoulliWeight`, `bitTableWeight`, `finiteRoutingWeight`, and `tableProbability` are explicit finite products and sums.
- `finiteRoutingWeight_sum` proves normalization; `finiteRoutingWeight_nonneg` proves nonnegativity for 0 ≤ p ≤ 1.
- `weighted_distinct_reads` is the basic finite-product averaging lemma.
- `terminal_average_local_miss` first fixes every selector and averages distinct terminal coordinates.
- `center_atom_weight_factorization` factors a center atom into its mass and exposed or unexposed coordinate laws.
- `joint_center_atom_all_miss` proves Pr(atom ∧ all miss) = Pr(atom)(1 − p/2)^J without dividing by atom mass or assuming independent adaptive paths.
- `actual_center_atoms_sum_one` supplies the normalized atom sum.
- `actual_routedSet_probability` and `actual_routedSet_expected_density` give the true occupancy probability and expected Lebesgue density p.

### ContinuumGeometric/NoDefaultProbability.lean

- `routeLeaf_eq_nondefault_iff_reads` describes each prescribed nondefault leaf event by its concrete selector reads.
- `nondefaultPathAddress_injective` supplies the distinct coordinates for that calculation.
- `actual_nondefault_leaf_probability` computes a leaf's probability.
- `actual_routeHasNoDefault_probability` and `actual_routeHasNoDefault_probability_rpow` give (1 − 2^(−(M−1)))^d for the actual route.

### ContinuumGeometric/RoutingCenterAtoms.lean

- `centerTableAssignment_satisfies_atom` constructs a canonical selector assignment for each center atom.
- `center_atom_default_vertex_exists` chooses one default vertex that works for every assignment in the atom.
- `actual_center_atom_partition` partitions any actual table event by these atoms.

Keeping one vertex per atom avoids an unnecessary union-bound factor for all vertices.

### ContinuumGeometric/RoutingChoices.lean

- `exists_branching_decay` chooses M so that pη(M − 1)/2 − 4 log 2 > 0.
- `exists_default_depth_budget` chooses finite d with no-default probability less than p.
- `exists_stable_gap_budget` chooses g after the finite edge count is known, with edge-count times 2^(3−g) less than p.

These choices precede U, L, the center, and the table outcome.

### ContinuumGeometric/EntropySchedule.lean

- `scheduledWindow` is Lmin + ⌈(4 log(U + 2) + max(C,0))/κ⌉.
- `scheduledWindow_log_lower` provides the required decay.
- `scheduledWindow_real_upper` and `scheduledWindow_affine_span_eventually` show the fixed affine tree span fits inside a sufficiently late U.
- `entropy_budget_of_log_lower` preserves the strict entropy inequality.
- `exists_late_entropy_schedule` obtains U and L satisfying both constraints and the prescribed lower guards.

### ContinuumGeometric/RoutingEntropy.lean

- `fair_selector_terminal_miss_exp_bound` and `fair_selector_terminal_miss_window_bound` bound the exact miss factor by exponential decay.
- `signature_entropy_exp_bound` retains 5120(P + 1)² exp(4 log 2 · ℓ), including the empty-candidate case.
- `signature_entropy_position_bound` retains the absolute position factor 46080 M²(U + 1)² and then uses κ > 0 and ℓ ≥ L.

### ContinuumGeometric/RoutingSchedule.lean

- `routingActivationRate` is η = 1/(2mK).
- `RoutingSchedule` packages the actual template together with active-count, original-tail, predecessor, coefficient, span, no-default, boundary, and entropy guards.
- `exists_routing_schedule` constructs this package in the order m, M, d, g, then U and L.
- `routingSchedule_node_entropy_lt` proves Q(P,ℓ) exp(−pη(M − 1)ℓ/2) < p for each actual vertex's candidate count and length.

The schedule is a constructed witness, not an assumed global object.

### ContinuumGeometric/RoutingLocalProbability.lean

- `actualLocalAllMiss_iff_active_tests` restricts the full candidate family to its active tests.
- `actual_fixed_parameter_joint_miss` instantiates the exact joint law using proved address separation.
- `actual_continuum_joint_miss_bound` applies the representatives and finite union bound.
- `scheduled_vertex_active_count` verifies J ≥ η(M − 1)ℓ with all schedule guards supplied.
- `scheduled_vertex_continuum_joint_miss_bound` concludes the atom-weighted continuum bound Pr(atom ∧ some-parameter all-miss) ≤ Pr(atom)p.

### ContinuumGeometric/RoutingStableProbability.lean

- `actual_missed_center_forces_vertex_miss` uses a stable center, its atom's default vertex, and the local-to-global implication to cover actual global failure.
- `actual_stable_bad_density_le` records the scheduled instability budget.
- `actual_stable_missed_center_probability_le` combines the atom-weighted continuum estimate with the proved no-default law to get probability at most 2p at every stable center.

## Lebesgue measure open repair and compactification

### ContinuumGeometric/ClosedProjection.lean

- `failureRelation`, `missedCenters`, and their membership theorems expose the existential parameter quantifier in the bad-center set.
- `PowerParams` is [s₀,s₁] × [1,2]; `powerPoint` is the exact real point map.
- `powerActivation` and `windowActivations` are open because their inequalities are strict.
- `isClosed_failureRelation` and `isClosed_missedCenters` use open activation, open hits, continuous point maps, and compact parameters.
- `powerMissedCenters`, `isClosed_powerMissedCenters`, and `measurableSet_powerMissedCenters` instantiate the actual finite routing tests.
- `power_tail_hits_open` and `power_repair_all_centers` use the infinite sequence to repair any center in an open cover of the closed missed-center set.

The repair index may be outside the finite test family while still satisfying the original N ≤ n.

### ContinuumGeometric/ZeroErrorBuffer.lean

- `zero_error_buffer_budget` supplies the strict scalar buffer budget used by the final measure proof.
- `double_open_buffers` and `double_buffer_contains_perturbation` are supporting buffer facts.

The current target has exactly zero approximation error. The existence of a perturbation helper does not establish a nonlinear-remainder theorem.

### ContinuumGeometric/ClosedRepair.lean

- `buffered_power_closed_repair` is a supporting specialization that combines open buffers with the closed-repair interface.

This imported helper module has no declaration in the audited stored proof closure of `geometric_main_target`. The final construction uses the directly instantiated `power_repair_all_centers` through `PeriodicRepair.lean`.

### ContinuumGeometric/PeriodicRepair.lean

- `integerPeriodization`, `unitDensity_integerPeriodization_le`, and `periodicGridSet_eq_integerPeriodization` handle canonical cells, negative lifts, and wrap.
- `volume_finiteGridCore` and `unitDensity_periodicGridSet` compute actual cell measure.
- `unitDensity_periodicGridSet_double_buffer_le` gives enlargement cost at most 4Gr.
- `unitDensity_grid_budget_double_buffer_lt` uses r = p/(8G), retaining a strict excess below p.
- `closed_onePeriodic_open_cover` constructs V ⊇ R with D(V) < D(R) + p using shrinking thickenings under finite restricted Lebesgue measure.
- `onePeriodic_powerMissedCenters` preserves periodicity of the actual closed bad set.
- `periodic_power_outcome_repair` turns D(B₂) + D(R) ≤ 5p into an actual open periodic all-center blocker with D(H) < 6p.

### ContinuumGeometric/RoutingMeasure.lean

- `finiteOutcomeProbability`, `finiteOutcomeExpectation`, and `expectedUnitDensity` connect finite real weights to extended-nonnegative Lebesgue integrals.
- `unitDensity_eq_lintegral_indicator` and `expectedUnitDensity_eq_lintegral_probability` integrate over the entire real interval [0,1).
- `expectedUnitDensity_le_stable_probability` combines stable-center probabilities with the measured exceptional set.
- `expectedUnitDensity_enlargement_le` transfers the finite-grid buffer bound to expectation.
- `exists_outcome_le_expectation` and `exists_outcome_density_add_le` select an actual finite outcome, allowing zero weights.
- `exists_powerRouting_outcome_density_add_le_of_stable` supplies D(B₂) + D(R) ≤ 5p from the actual closed missed-center sets and the stated bounds.

### ContinuumGeometric/RoutingAssembly.lean

- `globalRoutingWindows` includes every actual edge window, including default edges.
- `globalRoutingTests` and `globalRoutingTests_tail` give the finite original-tail tests.
- `routingFinestGrid`, `routingBufferRadius`, `routingInnerBuffer`, and `routingOuterBuffer` define the actual grid and open thickenings.
- `routingOuterBuffer_density_le` supplies the measured buffer cost.
- `actual_routing_blocker_of_stable_estimate` performs weighted outcome selection and all-center repair.
- `actual_routing_blocker_of_actual_stable_miss` supplies the actual measurable unstable set and its scheduled density bound, leaving only the displayed stable probability premise to be passed by `MainProof.lean`.

### ContinuumGeometric/CountableExhaustion.lean

- `CompactBlockerIndex` is the countable index type (K ≥ 2, k ∈ ℤ, N ∈ ℕ).
- `reflectedSet` and `unitDensity_reflectedSet` handle negative coefficients without losing measure at interval endpoints.
- `smallCompactBlockerSpec_open_exhaustion` chooses strictly summable positive budgets, includes every blocker and its reflection, and obtains one common open periodic U with D(U) < ε.
- `compact_complement_of_open_small` proves compactness of [0,1] ∖ U and the strict inequality `ENNReal.ofReal (1 - ε) < volume E`.
- `mainTarget_of_smallCompactBlockerSpec` is the precise conditional end-to-end bridge used by the final theorem.

### ContinuumGeometric/MainProof.lean

- `smallCompactBlockerSpec_proved` takes p = δ/12, constructs the routing schedule, supplies the proved stable probability estimate, and invokes the actual assembly to get D(H) < 6p = δ/2 < δ.
- `geometric_main_target` applies `mainTarget_of_smallCompactBlockerSpec` to that proved specification.

These are the two final unconditional results. Historical comments describing earlier conditional interfaces as `OPEN` do not add premises to them.

## Aggregate import and verification boundary

`ContinuumGeometric.lean` is the aggregate import file for the 45 modules above. It is convenient for clients; `ContinuumGeometric/MainProof.lean` is the focused entry point for the final theorem.

The supplied verification record reports clean rebuilds of the owned modules, exact-statement checks, an independent model-based source/construction review, and replay of the complete stored main proof closure in a fresh Lean kernel environment. The audited axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`; the record reports no `sorryAx` or added target axiom. Finite arithmetic regressions are supporting tests, not substitutes for the universal real-parameter proof.

These checks do not certify the separate stronger written theorem, computational feasibility of the noncomputable construction, novelty, or external professional-human mathematical peer review. Lean's foundational and implementation trust assumptions remain applicable.
