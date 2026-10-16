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

The present stage has ordinary Lean compilation evidence only. A finite-block
Berry--Esseen theorem, its required smoothing analysis, triangular-array bounds,
and the operational reliability converse are still work in progress. The
finite-law quantile result alone is not the optimal physical target theorem.
