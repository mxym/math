# Research claims -> exact Lean endpoints

Formal coverage is relative to the actual source statements, not green CI labels alone.

| Mathematical obligation | Lean endpoint | Current status |
|---|---|---|
| Partial-transpose convention bridge | `absolutelyPPT_right_iff` | Kernel checked for actual complex matrices. |
| Arbitrarily labeled eigenvalue witnesses | `appt_eigenvalue_witness_posSemidef` | Kernel checked with supplied permutation and injective corner. |
| Canonical ordered rank-two witness | `appt_sorted_rankTwo_witness`, `appt_sorted_rankTwo_determinant` | Complete necessary physical bridge; permutations constructed internally. |
| Largest eigenvalue bound | `appt_largest_eigenvalue_bound` | Complete necessary bound from actual density and APPT, not its equality/attainment classification. |
| Complete singular-state APPT locus | `singular_density_appt_iff_spectrum`, `singular_density_appt_iff_purity`, `exists_singular_appt_density` | COMPLETE necessity, sufficiency and actual singular attainment for density matrices with determinant zero. Independent CI 38189500302 and trust-zero replay passed. |
| Canonical least-diagonal star | `appt_sorted_shifted_star` | Physical placement and all leaf orientations constructed. No star budget supplied. |
| Positive sorted normalization pivot | `ordered_pivot_positive`, `paper_pivot_rank_bounds` | Trace, ordering and dimension obligations discharged in physical wrapper. |
| True logarithm inequalities and scalar nonlinear head | `entropyHead_le_two` and LogBounds | Previously checked scalar theorem, still explicitly retains scalar hypotheses. |
| Paper E9 from actual sorted APPT eigenvalues | `density_appt_paper_entropyHead` | COMPLETE for this finite theorem, including exact paper pivot. Only dimension, density and all-unitary APPT assumptions. |
| Ordinary PPT differs from APPT | Regression product-state declarations | Actual density/PPT and failure of APPT kernel checked. |
| Dimension-uniform physical contraction sufficiency | `absolutelyPPT_dimension_contraction` | COMPLETE finite theorem from actual P and I-P positivity; no spectral surrogate. Local and independent CI full builds and trust-zero replays passed (run 38131356027). |
| Actual projection-state attainment at every rank | `exists_projectionPlateau`, `exists_broad_plateau` | COMPLETE density, all-unitary APPT and exact purity. Not the upper bound or maximizing-spectrum classification. |
| Sharpness of the dimension-dependent constant | `antisymmetric_not_ppt` | Actual antisymmetric projection and exact maximally entangled test. Includes a trace-one 4x4 non-APPT regression. |
| Standard purity-ball physical sufficiency | `density_appt_of_purity_ball`, `density_complement_absolutelyPPT` | COMPLETE all-unitary sufficiency; not a necessary criterion in general. Physical counterexample to necessity audited. |
| Three-level 10x38 counterexample | Scalar SOS and rational gaps | Joint projection-plus-spike quantum sufficiency still missing; contraction sufficiency alone does not prove this membership. |
| All ordered gap arrangements | `appt_all_ordered_pair_witnesses`, `appt_ordered_gap_square_bound` | Complete physical finite statements; placements constructed for every edge bijection. |
| Triangular row inequality | `triangular_degree_square` | Complete in arbitrary dimension with explicit entrywise sign, symmetry and row-order hypotheses. |
| Actual sorted gap square budget | `density_appt_pair_gap_square_sum` | Complete necessary bound from density and APPT, including exact paper pivot and edge count. |
| Baseline-sensitive graph budget | `baseline_graph_refined_budget` | Complete generic finite inequality including the exact cross term; actual spectral baseline instantiation is now proved in `SpectralBaseline`. |
| Sorted centered variance | `sorted_centered_variance` | Complete for arbitrary decreasing real vectors of sum one and 2R<=D; now connected to actual quantum purity by `FinitePurity`. |
| Actual finite purity bound | `density_appt_finite_purity_bound` | COMPLETE finite physical inequality with the exact spectral pivot, graph and moment dependencies discharged; local and independent CI build and trust-zero replay passed; dimension-only normalization is now proved separately below. |
| Dimension-only normalization | `density_appt_normalized_purity_bound`, `density_appt_dimension_only_upper` | COMPLETE actual-state inequalities; the latter assumes only 8<=m<=n, density and APPT. |
| Uniform growing-small-dimension purity upper half | `appt_uniform_asymptotic_upper` | COMPLETE quantified epsilon theorem: one threshold works for every n>=m and all actual APPT density matrices. Local and independent CI fresh builds and trust-zero replays passed (run 38141972563); matching lower/equality is not proved. |
| Finite-dimensional physical compactness and attainment | `isCompact_physicalAPPTStates`, `exists_appt_purity_isGreatest` | COMPLETE, independent CI 38162415802; existence only, not numerical evaluation. |
| Entire attainable purity interval and unique minimum | `apptPurityValues_eq_Icc`, `density_minimum_purity` | COMPLETE for actual density/APPT states. |
| Strict-mixture rigidity and fixed-dimensional optimizing subsequences | `appt_maximizing_mixture_rigid`, `appt_near_maximizers_subsequence` | COMPLETE finite statements; not dimensional rigidity or graph-limit compactness. |
| Exact rectangular maximum and all maximizers | No final endpoint | Physical broad-plateau attainment is now proved; outer-polytope construction, vertex optimization and maximizing-spectrum classification remain. |
| Multiscale and two-ended graph limits | No final endpoint | Compactness, simultaneous levels, nested witnesses and order of limits missing. |
| Complementary fixed-m asymptotic | `appt_fixed_local_purity_sup_tendsto` | COMPLETE for the physical supremum: nonempty bounded state set, both finite bounds, actual projection-state rounding, positive scaling and filter limit. Independent build and trust-zero replay passed (run 38153054623). Finite optimizer/classification not claimed. |
| Fixed-local first excess-purity coefficient | `appt_fixed_local_excess_sup_tendsto` | COMPLETE: subtracting the maximally mixed baseline from the physical fixed-local supremum gives the exact limit (1/(m^2-1)) after multiplication by (mn). Kernel replay uses only standard Lean axioms. |
| Two-level plateau optimization | `plateauScaledPurity_le_continuous`, `plateauScaledPurity_even_rank_max` | COMPLETE within the projection-plateau family: an exact square-deficit identity gives the continuous upper value, and the even-rank case attains it at rank (((m-1)n)/2). This does not classify all APPT maximizers. |
| Upper half over every dimensional regime | `appt_total_dimension_uniform_upper` | COMPLETE quantified physical upper bound: one total-dimension threshold covers every 2<=m<=n and actual APPT state. Independent build and trust-zero replay passed (run 38153054623); growing-m matching lower remains. |
| Uniform purity and Renyi entropy extrema | No final endpoint | The all-total-dimension purity upper half and fixed-m purity supremum limit are verified above. Matching growing-m lower constructions, full extremal equivalence, and unrestricted entropy extrema remain unclosed. |
| Rigidity and equality classifications | No final endpoint | Saturation, empirical/outlier limits and attaining constructions still missing. |

No `sorry`, custom axiom, untrusted `native_decide`, assumed main conclusion, or finite enumeration is used to turn an unclosed row into a verified theorem.
