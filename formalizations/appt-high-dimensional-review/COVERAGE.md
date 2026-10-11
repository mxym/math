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
| Dimension-uniform physical contraction sufficiency | `absolutelyPPT_dimension_contraction` | COMPLETE finite theorem from actual P and I-P positivity; no spectral surrogate. Local full build and kernel replay passed. |
| Actual projection-state attainment at every rank | `exists_projectionPlateau`, `exists_broad_plateau` | COMPLETE density, all-unitary APPT and exact purity. Not the upper bound or maximizing-spectrum classification. |
| Sharpness of the dimension-dependent constant | `antisymmetric_not_ppt` | Actual antisymmetric projection and exact maximally entangled test. Includes a trace-one 4x4 non-APPT regression. |
| Three-level 10x38 counterexample | Scalar SOS and rational gaps | Generic quantum sufficiency bridge not yet formalized. |
| Unrestricted triangular finite purity bound | No final endpoint | General sorted edge assignment, row inequality, variance and normalization still needed. |
| Exact rectangular maximum and all maximizers | No final endpoint | Physical broad-plateau attainment is now proved; outer-polytope construction, vertex optimization and maximizing-spectrum classification remain. |
| Multiscale and two-ended graph limits | No final endpoint | Compactness, simultaneous levels, nested witnesses and order of limits missing. |
| Uniform purity and Renyi entropy extrema | No final endpoint | The finite entropy-head theorem alone does not prove the global minima/maxima or their limits. |
| Rigidity and equality classifications | No final endpoint | Saturation, empirical/outlier limits and attaining constructions still missing. |

No `sorry`, custom axiom, untrusted `native_decide`, assumed main conclusion, or finite enumeration is used to turn an unclosed row into a verified theorem.
