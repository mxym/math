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

`Deviation.JointTypical` and `PrefixTail` prove a joint-log-likelihood change of
measure from actual finite iid laws. `EntropyPerturbation` proves approximation
of the entropy-constrained divergence infimum from the strict entropy side by
mixing with the uniform law on the positive support. `Deviation.Reliability`
therefore proves matching source-subset tail estimates at every moving rate
`c_k → c` with `H(p)<c<log |supp(p)|`, allowing singular spectra. The converse
holds uniformly over every subset of size at most `exp(k c_k)`; an explicit
low-empirical-entropy subset proves the other direction. A density-matrix
endpoint identifies the support-size boundary with the true matrix rank.

`Deviation.PrimalPerturbation` proves that every positive-support primal
variational optimum has arbitrarily close feasible trials with entropy strictly
below the full alphabet maximum, including the flat full-rank input. Its proof
uses the strict Gibbs inequality and a small point-mass mixture only at the
uniform endpoint.

`FourierMoment`, `FourierPower`, and `FourierIID` prove quantitative cubic
characteristic-function remainder bounds, finite iid tensor factorization,
Gaussian damping on an explicit frequency range, and the normalized estimate

`|φ_k(t) - exp(-t²/2)| ≤ 4 |t|³ T/(V^(3/2) sqrt k) + t⁴/(4k)`

for `t²≤k`, directly for the constructed finite iid measure. `Triangular` and
`TriangularInformation` use these estimates and Lévy continuity to prove the
Gaussian approximation uniformly over all real information thresholds for
varying finite alphabets, laws, and variances whenever
`T/(V^(3/2) sqrt k) → 0`. Actual complex density spectra with changing dimensions
are instantiated internally. `GaussianRegularity` proves the exact Gaussian
CDF Lipschitz constant `1/sqrt(2π)`; `UniformGaussian` proves the distinct CDF
smoothing comparison in terms of Lévy--Prokhorov distance.

`LyapunovMoment` proves the moment comparison `T ≥ V sqrt V` internally.
`NormalizedDamping` strengthens the quantitative normalized estimate to

`|φ_k(t) - exp(-t²/2)| ≤ 5 β_k |t|³ exp(-t²/8)`

for `k≥2` and `16 β_k |t|≤1`, with `β_k=T/(V^(3/2) sqrt k)`.
`FourierIntegral` proves integrability of the divided error and the actual
truncated Fourier integral bound `∫_{-R}^R |φ_k-G|/|t| ≤ 5 β_k C₂` at
`R=(16 β_k)⁻¹`. The absolute constant `C₂=∫ t² exp(-t²/8) dt` is internally
proved finite and is independent of the law, alphabet, variance, and block.

The present stage has ordinary Lean compilation evidence only. A finite-block
Berry--Esseen CDF rate still requires the Esseen Fourier smoothing inequality;
the proved qualitative triangular approximation is not a substitute for that
finite error rate. The physical integration of the new tail and triangular
bounds is performed in separate scopes. Earlier
independent audits do not automatically cover this separate source scope.
