# Entropy-head stability: exact formal coverage

This supplements, rather than replaces, the original high-dimensional coverage table. Independent CI **38514601775** verified source **cb81f0fa1f82028c148c317c61b2ebfa786809ea**. Evidence and exact source binding: `verification/entropy-ci-cb81f0fa/`.

| Obligation | Lean endpoint | Verified scope |
|---|---|---|
| Dimension-independent head-outlier bounds | `entropyHead_outlier_bounds` | Cubic positive outlier <=300 Delta and negative outlier <=72 Delta under explicit scalar hypotheses. |
| Strict finite head bound | `entropyHead_lt_two` | Every finite admissible scalar head has H<2; no finite equality is claimed. |
| Physical hypotheses and exact paper pivot | `density_appt_paper_head_conditions` | All signs, ordering, pivot positivity and shifted-star constraints follow from actual density and all-unitary APPT. |
| Full trace normalization | `trace_normalized_contrast` | Trace one is used explicitly; the pivot is not substituted by 1/(mn). |
| Actual all-eigenvalue quantitative bound | `density_appt_head_spectral_cubic` | If the actual head deficit is <=1/144, every normalized eigenvalue obeys |D lambda_i-1|^3<=11904 Delta. |
| Positive spectrum | `density_appt_head_positive_spectrum` | The same small-deficit assumption implies positivity of every actual eigenvalue. |
| Dimension-varying uniform flatness | `appt_entropy_head_saturation_flat` | Head deficit tending to zero implies uniform convergence of all D lambda_i to one, with actual matrices of varying dimensions. |
| Full entropy extremizer implies head saturation | No endpoint | REMAINS OPEN IN THE FORMALIZATION; not assumed proved by this checkpoint. |
| Complete von Neumann/Renyi entropy extrema and all rigidity claims | No endpoint here | REMAIN SEPARATE; the head theorem does not certify the full analytic program. |

The separate runner `reproduce_entropy_stability.py --fresh` builds the entire selected dependency closure and replays 25 roots and 39,730 declarations in an empty trust-zero kernel. Three exact-type forged-proof controls are rejected. Only the three standard axioms occur. The earlier complete purity proof and its 154-input manifest are unchanged; this checkpoint has its own 33-input manifest.
