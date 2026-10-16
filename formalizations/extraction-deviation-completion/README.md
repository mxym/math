# Deviation and fixed-error completion

Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
This is a new, separate source scope; all earlier audit scopes are frozen.

`Deviation.Gaussian` constructs the unique inverse of the actual centred Gaussian
CDF on `(0,1)`, proves strict monotonicity and continuity from the Gaussian
measure, and proves complement symmetry and standard-deviation scaling.

`Deviation.FiniteQuantile` defines an attained quantile of an actual finite
weighted law and proves its exact threshold characterization.

`Deviation.InformationQuantile` proves the fixed-error inverse CLT for the
actual finite iid information spectrum, including zero-probability letters.
Neither a CLT conclusion nor a Gaussian approximation is a caller hypothesis.

`Deviation.RoundedTarget` constructs the actual natural integer targets and
proves their second-order expansion, including harmless early local caps.
`Deviation.OperationalQuantile` proves a target-uniform exclusion bound for all
actual finite-Kraus PPT protocols, without imposing a local target cap on the
converse. `Deviation.FixedErrorTarget` then proves that both the state-aware PPT
maximum and the maximum achieved by the fixed common local protocol satisfy

`(log K_opt(k,ε) - k C) / sqrt k → sqrt(V) Φ⁻¹(ε) / 2`.

The maximum is attained for all sufficiently large blocks. The proof does not
assume monotonicity of the common protocol in its target, a probability limit,
or existence of a maximizing channel. Its hypotheses are a fixed actual
density, positive varentropy, `0<C<log m`, `C<log n`, and `0<ε<1`.

The present stage has ordinary Lean compilation evidence only. A finite-block
Berry--Esseen theorem, its required smoothing analysis, triangular-array bounds,
and the operational reliability converse remain work in progress. Earlier
independent audits do not automatically cover this separate source scope.
