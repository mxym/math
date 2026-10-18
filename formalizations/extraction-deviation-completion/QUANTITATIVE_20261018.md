# Finite quantitative continuation (2026-10-18)

Status: BUILD_ONLY. Aggregate `lake build` succeeded, 4046 jobs, with Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Log: `D:/math/tmp/extraction-resume-20261018/build-logs/20261018T144804351289Z-extraction-deviation-completion.log`. This is not independent kernel/audit evidence.

The quantitative modules are now compiled and included in `Deviation.lean`:

- `informationQuantile_berryEsseen_bracket` bounds the attained natural finite-spectrum quantile between Gaussian quantiles at epsilon minus/plus the computed Berry--Esseen error. The finite BE bound is proved internally; spectra may contain zeros.
- `universalBlockProtocol_berryEsseen`, `protocol_berryEsseen_upper`, `universalTarget_of_log_le`, and `pptTarget_log_le` give finite actual-protocol and inverse target bounds, with the exact intrinsic orbit loss and free smoothing length. Achievability retains both local natural-number caps; the PPT converse has no cap premise.
- `finiteCappedTarget_achievable` directly constructs the positive floor-exponential target with both local caps. `log_natFloor_exp_bounds` costs at most log 2 even at budget zero; `finiteCappedTarget_log_lower` retains the exact clipped logarithmic budget.
- `protocol_berryEsseen_lower_of_entropyMass` takes any actual finite Kraus PPT protocol's independently established entropy-prefix lower bound with coefficient a >= 0 and cutoff c. It returns a times (Phi((kc-kH)/sqrt(kV)) minus the computed BE error). This is the interface for the reserved family and does not import or modify the operational completion package.
- `compressionLoss_le` supplies an explicit dimension-dependent bound: log 4 + (D^2-1) log(k+D^2) + D log(k+1).
- `triangular_informationQuantile_gaussian` proves inversion for changing finite distributions and variances under the computed Lyapunov ratio tending to zero.
- `triangular_universal_gaussian_error` proves the actual common family's Gaussian error tends to zero, with arbitrary moving target thresholds, under the explicit moment ratio, diverging sqrt(kV), and orbit-loss/sqrt(kV) conditions, with both output caps retained.

These extend the intrinsic orbit-compression implementation. They do not identify it with the manuscript's Schur implementation, assert sharp dimension thresholds beyond the displayed sufficient loss condition, or close the abstract CP-to-Kraus model bridge.

The final minimal sufficient-condition extension is `Deviation.QuantitativeConditions`:
`dimensionLossBound D k = log 4 + (D^2-1) log(k+D^2) + D log(k+1)`.
`triangular_universal_gaussian_of_variance_floor` derives the previous actual
protocol error theorem from a single fixed positive variance floor, actual third
centered absolute moment T_k/sqrt(k) -> 0, and dimensionLossBound(D_k,k)/sqrt(k) -> 0.
No alphabet restriction, moment/variance approximation, or final operational limit
is supplied as a premise. Both natural output caps are retained at every block.
The corresponding aggregate build passed 4047 jobs; log:
`D:/math/tmp/extraction-resume-20261018/build-logs/20261018T150004745341Z-extraction-deviation-completion.log`.

`verification/build-only-20261018/` contains this new continuation's exact 24
theorem roots, all 28 named declarations, source hashes, and the ordinary
elaborator dependency report. Every declaration uses only propext,
Classical.choice, Quot.sound, or no axioms. The report is not independent
verification and does not extend any frozen earlier scope.
