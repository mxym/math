# Research claims -> exact Lean endpoints

Formal coverage is relative to the actual source statements, not green CI labels alone.

| Mathematical obligation | Lean endpoint | Current status |
|---|---|---|
| Partial-transpose convention bridge | `absolutelyPPT_right_iff` | Kernel checked for actual complex matrices. |
| Arbitrarily labeled eigenvalue witnesses | `appt_eigenvalue_witness_posSemidef` | Kernel checked with supplied permutation and injective corner. |
| Canonical ordered rank-two witness | `appt_sorted_rankTwo_witness`, `appt_sorted_rankTwo_determinant` | Complete necessary physical bridge; permutations constructed internally. |
| Largest eigenvalue bound | `appt_largest_eigenvalue_bound` | Complete necessary bound from actual density and APPT, not its equality/attainment classification. |
| Matrix singularity -> exact ordered spectrum | `density_appt_singular_spectrum` | Complete necessary statement from `A.det=0`; converse attainment not included. |
| Canonical least-diagonal star | `appt_sorted_shifted_star` | Physical placement and all leaf orientations constructed. No star budget supplied. |
| Positive sorted normalization pivot | `ordered_pivot_positive`, `paper_pivot_rank_bounds` | Trace, ordering and dimension obligations discharged in physical wrapper. |
| True logarithm inequalities and scalar nonlinear head | `entropyHead_le_two` and LogBounds | Previously checked scalar theorem, still explicitly retains scalar hypotheses. |
| Paper E9 from actual sorted APPT eigenvalues | `density_appt_paper_entropyHead` | COMPLETE for this finite theorem, including exact paper pivot. Only dimension, density and all-unitary APPT assumptions. |
| Ordinary PPT differs from APPT | Regression product-state declarations | Actual density/PPT and failure of APPT kernel checked. |
| Dimension-uniform physical contraction sufficiency | `absolutelyPPT_dimension_contraction` | COMPLETE finite theorem from actual P and I-P positivity; no spectral surrogate. Local and independent CI full builds and trust-zero replays passed (run 38131356027). |
| Actual projection-state attainment at every rank | `exists_projectionPlateau`, `exists_broad_plateau` | COMPLETE density, all-unitary APPT and exact purity. Not the upper bound or maximizing-spectrum classification. |
| Sharpness of the dimension-dependent constant | `antisymmetric_not_ppt` | Actual antisymmetric projection and exact maximally entangled test. Includes a trace-one 4x4 non-APPT regression. |
| Three-level 10x38 counterexample | Scalar SOS and rational gaps | Generic quantum sufficiency bridge not yet formalized. |
| All ordered gap arrangements | `appt_all_ordered_pair_witnesses`, `appt_ordered_gap_square_bound` | Complete physical finite statements; placements constructed for every edge bijection. |
| Triangular row inequality | `triangular_degree_square` | Complete in arbitrary dimension with explicit entrywise sign, symmetry and row-order hypotheses. |
| Actual sorted gap square budget | `density_appt_pair_gap_square_sum` | Complete necessary bound from density and APPT, including exact paper pivot and edge count. |
| Baseline-sensitive graph budget | `baseline_graph_refined_budget` | Complete generic finite inequality, including the exact cross term; the spectral baseline instantiation remains. |
| Sorted centered variance | `sorted_centered_variance` | Complete for arbitrary decreasing real vectors of sum one and 2R<=D; not yet the assembled physical purity bound. |
| Actual finite purity bound | `density_appt_finite_purity_bound` | COMPLETE finite physical inequality with the exact spectral pivot, graph and moment dependencies discharged; local fresh build and trust-zero replay passed. Dimension-only normalization not yet included. |
| Exact rectangular maximum and all maximizers | No final endpoint | Physical broad-plateau attainment is now proved; outer-polytope construction, vertex optimization and maximizing-spectrum classification remain. |
| Multiscale and two-ended graph limits | No final endpoint | Compactness, simultaneous levels, nested witnesses and order of limits missing. |
| Uniform purity and Renyi entropy extrema | No final endpoint | The finite entropy-head theorem alone does not prove the global minima/maxima or their limits. |
| Rigidity and equality classifications | No final endpoint | Saturation, empirical/outlier limits and attaining constructions still missing. |

No `sorry`, custom axiom, untrusted `native_decide`, assumed main conclusion, or finite enumeration is used to turn an unclosed row into a verified theorem.
