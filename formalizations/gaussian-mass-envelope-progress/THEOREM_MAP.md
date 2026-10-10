# Paper → necessary lemmas → Lean statements

Initial audit baseline: main `586ed2e`; synchronization baseline for this new
package: `0071871965aed1e37d55c9c025079094da616910`.
Target paper: `research/gaussian-centroid-mass-envelope/paper.md`.

| Paper statement | Necessary mathematics | Lean entry | Status in this revision |
|---|---|---|---|
| Lemma 2, equation (8) | Actual tail calculus, two truncated moments, variance, derivative comparison, quantile existence and uniqueness | `GaussianMeasureBridge.squared_hazard_log_lipschitz` | PASS: clean build and empty-kernel replay |
| One-cell upper bound, equation (14) | Actual unit projection law, threshold rearrangement, Bochner moment, exact indicator bridge | `GaussianMeasureBridge.measurable_set_moment_bound` | PASS: clean build and empty-kernel replay |
| Global upper inequality for every admissible partition | Sum of the single-cell bounds on the original measurable sets | `GaussianMeasureBridge.prescribed_mass_measurable_sets_bound` | PASS: clean build and empty-kernel replay |
| Terminal-cell inequality (16b) | Actual Gaussian exponential moment and integrated tangent inequality | `GaussianMeasureBridge.gaussian_profile_entropy_bound` | PASS: clean build and empty-kernel replay |
| Lemma 3, equation (10) | Ordered weighted covariance and residual entropy | Not yet supplied | Open formalization gap |
| Lemma 1 and equation (7a) | Independent coordinate thresholds, exact cell masses and all moments | Not yet supplied | Open formalization gap |
| Full Theorem 4, equation (13) | Staircase construction, preceding lemmas, lower estimate, dimension extension, exact supremum definition/assembly | Not yet supplied | NOT a complete Lean theorem |
| Two-log-scale refinements | Mills bounds and scalar estimates | Not selected | Outside present coverage |

A theorem about all measurable set families is stronger than the corresponding
partition upper inequality, but the paper's supremum object and the two-sided
main theorem are not silently counted as already formalized.

The Gaussian multi-bubble theorem needed by the four-cell/all-k direction is
not available in this project as a proved Lean input. That direction was not
selected here. No hypothesis packaging that external theorem is counted as a
proof.

Evidence: source `46f8894`, CI run `38025117038`, 9 modules, 47 roots, 53,046 replayed declarations. See `evidence/ci-38025117038/README.md`.
