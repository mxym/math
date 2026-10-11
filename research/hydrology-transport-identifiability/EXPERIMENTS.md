# Experiments, findings and unresolved issues

All observations in these experiments are synthetic. Exact rational calculations
and floating-point diagnostics have different evidentiary roles.

## 1. Four-store all-forcing-equivalent networks

The continuous physical family theta in [-0.1,0.125] is certified in THEOREMS.md
and exact.py; no fitting optimizer constructs its water equivalence. It preserves
all water response histories by similarity and fixed output/input anchors.
The synthetic daily forcing has 730 days, seed 20261011, Gamma-distributed storm
amounts and five environmental-demand levels. Daily propagators and integrated
fluxes use matrix exponentials, avoiding a time-discretization drift explanation.

Compared with theta=0, theta=0.1 changes cumulative store-1-to-store-3 flow from
208.0521 to 40.3782 catchment-equivalent mm (-80.59%), and store-1-to-store-4 flow
from 104.0261 to 201.8908 mm (+94.08%). Discharge, ET and total-storage maximum
absolute differences are below 6.4e-14, consistent with roundoff. Exact identity
is proved separately. The retained-solute relative RMS difference is only 0.3727%.
The numerical water-balance residual is below 2.2e-13 for this comparison.

This is a counterexample to interpreting a fitted internal transfer as uniquely
learned from these water outputs within this flexible model class. It is not a
counterexample to any existing hydrological model's predictive accuracy.

## 2. Material contrast and restricted noisy fitting

Let rho describe the tracer's environmental loss relative to water's. For rho
0,0.5,0.9,0.99,1, the relative RMS difference between theta=0 and theta=0.1 is
approximately 0.003727,0.001410,0.0002574,0.00002533, and 3.55e-16. The exact
structural ambiguity returns at rho=1; small contrast also causes weak signals.

With retained tracer and the first 365 days, noiseless one-dimensional fitting
recovers theta about -8.1e-15. In 20 independent noise realizations with standard
deviation 1% of the training tracer RMS, fitted theta has mean -0.00334 and
standard deviation 0.01183. This searches only the known one-dimensional
water-equivalence family. It does not establish full-network parameter recovery.
The second year's outputs are retained but no competitive forecast benchmark or
independent field holdout validation is claimed.

The derivative-kernel Hankel condition number is about 3.55e8. This was a useful
failure diagnostic: a structural identification formula is not automatically a
practical estimator for noisy data.

## 3. Finite-time alternative

Theorem 5 replaces response derivatives by controlled finite-dwell responses.
Its estimator is passed only those responses, their time spacings and model
order; the true loss eigenvalues and internal rates are not supplied. Baseline
spacings 1,3,5,10,15,20 days are tested, with a one-day middle dwell.

At spacing 10 days, maximum absolute errors over all reconstructed coefficients
are about 1.8e-11 (theta=0) and 7.2e-11 (theta=0.1). The sufficient anti-aliasing
bound is satisfied: delta times the maximum generator 1-norm is 0.30 or 0.304,
both below log(2). However, the sampled Hankel condition number is still 2.30e6.
Wider or narrower spacings do not monotonically improve conditioning. This
resolves the need for response derivatives, not the general noisy inversion
problem. The complete prespecified spacing sweep is retained.

## 4. Experiments targeted at invisible directions

At the baseline, the anchored water-equivalence space has dimension three.
For generator X in this space, the informative retained-tracer sensitivity is
xi'=A xi+u[De,X]z, J_X=q^T xi, with zero initial xi. This is derived in the
written proof and integrated directly in design.py.

A unit tracer pulse and 90 daily outlet samples are used. Across the entire
finite family of 61 schedules that turn demand from zero to one at day 0..60,
the largest smallest singular value occurs at day 23. Relative to demand
always on, the smallest singular value improves by 9.44 times and its square
(the weakest Fisher-information eigenvalue under equal independent noise)
by 89.15 times. Larger sensitivity modes do not all improve. With demand zero
throughout, the contrast vanishes entirely.

This is a local, synthetic, finite-family design result. It does not identify
an optimal field schedule, apply safety/regulatory advice about tracer release,
or demonstrate a universal 89-fold benefit.

## 5. What changed during the investigation

A generic equifinality result was rejected as insufficiently novel. The idea
that every tracer automatically resolves ambiguity was also rejected: an ideal
water-following label has the same generator and cannot do so here. The
physically differing environmental-loss operator supplies the useful contrast.
The first derivative-based reconstruction was found poorly conditioned; a
finite-dwell formulation was added but numerical conditioning remains a real
limitation. Literature checks found close classical compartmental symmetry work,
so historical-priority claims were explicitly withheld.

## 6. Most valuable next scientific test

A controlled small compartment/soil-column system with independently measured
internal water inventories is the appropriate falsification test before any
large-catchment claim. Compare a static-transfer model, an affine-demand model,
and their joint water/material versions. Conceal internal observations during
fitting, then test whether the identified model recovers those withheld states
and responses to a new controlled forcing. Verify material balance and uptake/
sorption assumptions first. A positive result would motivate, not replace,
subsequent catchment-scale tests.

The most serious remaining mathematical task is stable, constrained inference
under noise and repeated contrasts, including realistic deep stores with no ET.
The most serious novelty task is an independent systems-identification review.
