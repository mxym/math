# Intrinsic Gaussian facet coefficients and singular limits

**Unconditional partial formalization. The sharp four-cell global inequality
and complete equality classification are NOT proved by this package.**

## New actual analytic chain

`MaskedTail`, `PairSlice`, `PairSliceIntegral`, and `PairMassDerivative`
prove an off-diagonal competitor-price derivative at every positive-mass
winning diagram, without an affine-independence assumption. In a fixed
positive pair chart, changing only b_j moves exactly one cutoff, while all
other winning inequalities remain in a measurable mask. Fubini uses the
actual standard Gaussian product law. The masked Gaussian tail has the
uniform Lipschitz constant phi(0). Positive-mass triple-tie exclusion makes
its unstable cutoffs a Gaussian-null set, including zero restricted normals
with nonzero offsets. Dominated differentiation gives

    d/dt gamma(C_i(v,b+t e_j)) at t=0 = pairChartWeight(v,b,i,j), i != j.

`IntrinsicWeights` defines the off-diagonal coefficient from this original
mass derivative, proves its existence, and identifies it with every positive
orthogonal chart integral. The diagonal is zero. Equality of different
charts follows from uniqueness of the actual derivative; it is not assumed.

`IntrinsicContinuity` proves joint continuity of these intrinsic coefficients
at positive-mass diagrams, including singular scores and disappearing facets.
For a convergent balanced sequence with distinct limiting scores, the limit
retains its prescribed positive masses and every intrinsic weight converges.
The limiting masses are derived by Gaussian dominated convergence.

`IntrinsicFlux` identifies these coefficients with the constructed positive
symmetric Gaussian flux in every affine-independent diagram. Passing to the
limit gives the actual Bochner first-moment flux identity and symmetry at a
possibly singular limit of balanced affine-independent diagrams.
`IntrinsicBoundary` proves convergence of the entire Laplacian matrix and
positive semidefiniteness at the limit.

Main entries:

```lean
GaussianFour.actual_competitor_price_derivative
GaussianFour.positive_pair_charts_compatible
GaussianFour.continuousAt_intrinsicPairWeight
GaussianFour.balanced_intrinsic_weights_limit
GaussianFour.balanced_simplicial_limit_intrinsic_flux
GaussianFour.balanced_simplicial_limit_laplacian
```

The last two statements concern d+2 scores in R^(d+1); d=2 is the four-cell
intrinsic three-dimensional problem. Their hypotheses explicitly include
affine-independent approximants, converging scores and prices, prescribed
positive masses, and distinct limiting scores. They do not assume limiting
mass constraints, moment convergence, facet convergence or limiting flux.
They do not construct the global variational critical sequence.

## Integration and scope

Baseline: f4753da178989d9f0ed3e8323817c9969e20ff4c.
`GaussianFour/WinningLimits.lean` is byte-identical source reuse from commit
971408e73a373d67d8b86ad49a7f9af65a53b567, originally
`formalizations/gaussian-four-global-progress/GaussianWinningLimits.lean`.
Its namespace is preserved. This is integration and fresh verification of
parallel work, not a new proof claim. The other eight modules are new.
See BOUNDARY_PROVENANCE.json for exact source binding.

Coordinate-independent coefficients computed in positive orthogonal charts
are now proved. Identification with the exact Gaussian surface measure and
perimeter used by geometric lower bounds remains separate. The construction
and control of regularized covariance critical sequences, remaining spectral
transport, rank-one extraction, complete rank-two exclusion, covariance
higher regularity/Hessian, constrained mountain pass, geometric lower bounds,
the tetrahedral arctangent evaluation, and the final sharp theorem and full
equality classification remain. No missing input is introduced as an axiom.

## Verification

The 105-module, 631-root package is undergoing fresh source-bound verification.
Baseline logs are not substituted for this extension's build or replay.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. mxymmxym1@gmail.com.
ORCID 0009-0000-3864-3536. No external funding; AI-assisted research.
Existing licenses and third-party notices remain in force. Original additions
retain all rights not otherwise granted. No external peer review is claimed.
