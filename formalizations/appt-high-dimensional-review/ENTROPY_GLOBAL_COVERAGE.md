# Full entropy upper and rigidity coverage

Independent run 38536151448 checked source d2a9ff63afb0e3134233d7df345baa9013f5c4ed. The selected 75-input closure and literal evidence are retained in verification/entropy-ci-d2a9ff63/.

| Obligation | Exact Lean endpoint | Scope |
|---|---|---|
| Head-retaining physical variance | density_appt_head_retained_variance | COMPLETE from actual density/APPT; no graph budget assumed |
| Full logarithmic and quadratic centering | spectrum_entropy_centering; spectrum_entropy_remainder_identity | COMPLETE including zeros and arbitrary positive pivot |
| Nonexceptional Taylor remainder | density_appt_full_entropy_taylor_bound; density_appt_dimension_entropy_bound | COMPLETE finite bounds; dimension radii are proved |
| Full von Neumann upper half | appt_vonNeumann_fixed_aspect_upper | COMPLETE at fixed finite aspect ratio, arbitrary actual state sequence |
| Full entropy saturation implies head saturation | appt_full_entropy_head_saturation | COMPLETE; head saturation is a conclusion |
| Full entropy saturation implies flat spectrum | appt_full_entropy_saturation_flat | COMPLETE uniform control of every normalized eigenvalue |
| Full entropy versus flat optimal purity | appt_entropy_saturation_iff_flat_purity | COMPLETE equivalence of coefficient saturation; not existence of saturating states |
| Matching entropy lower construction | No endpoint | NOT COMPLETE |
| Fixed-local/all-regime minimum entropy and other Renyi orders | No endpoint here | NOT COMPLETE |

These statuses do not reinterpret the independently complete leading purity law as an entropy proof. Independent CI is not external mathematical peer review.
