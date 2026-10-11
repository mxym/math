# Paper claim -> mathematical obligation -> Lean coverage

This is a semantic coverage map, not a list of tasks all marked complete.

| Working-proof obligation | Lean endpoint | Status and remaining quantifiers |
|---|---|---|
| Either partial-transpose convention has the same PSD test | `absolutelyPPT_right_iff` | Kernel-checked for actual complex matrices. |
| Actual global-unitary eigenvalue witness in arbitrary rectangular dimensions | `appt_eigenvalue_witness_posSemidef` | Kernel-checked for every supplied permutation and injective corner map. |
| Positive central-diagonal star budget | `psd_star_bound`, `appt_eigenvalue_star_bound` | Kernel-checked. Physical endpoint still requires the label inequalities to be established. |
| Entropy proof E8, least-eigenvalue-centered sorted star | Physical star wrapper | Exact sorted-label permutation and dimension-based existence still not constructed. |
| Actual logarithm estimates and quartic strict barrier | `entropy_negative_bound`, `entropy_positive_gap_bound`, `entropy_head_outlier_margin` | Kernel-checked, including the negative endpoint. |
| Entropy proof E9, full exceptional-head bound | `entropyHead_le_two` | Kernel-checked for arbitrary finite length from the stated sign, order and star budget assumptions. |
| APPT -> nonlinear head with specified placements | `appt_eigenvalue_entropyHead_bound` | Kernel-checked. Does not assume the star inequality, but still needs canonical sorted placement. |
| Three-level counterexample physical membership | Scalar `multilevel_sos_nonneg` plus rational gaps only | All-unitary quantum sufficiency not yet formalized. |
| Unrestricted finite triangular purity inequality | No endpoint yet | Ordered placement, graph norm, variance and normalization must be linked. |
| Exact rectangular optimum and all equality cases | No endpoint yet | Outer-polytope vertex theorem, optimization, physical attainment and equality classification missing. |
| Lacunary graph limits and two-ended hierarchy | No endpoint yet | Compactness, simultaneous levels, nested lower witnesses and limit order missing. |
| Uniform asymptotic purity and entropy theorems | No endpoint yet | No complete filter-limit theorem for these genuine maxima/minima. |
| Phase and entropy-order rigidity | No endpoint yet | Defect saturation, outlier/empirical limits and constructions missing. |

No `sorry`, custom axiom or native-decide shortcut closes these gaps. Independent review means rechecking the argument and its representation; it does not mean external peer review by another researcher.
