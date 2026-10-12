# Manuscript-to-Lean correspondence — partial formalization

Reference: `research/gaussian-balanced-four-global/paper.md`. Source import
provenance: `UPSTREAM_PROVENANCE.json`; exact owned compilation order:
`MODULES.json`; audited declarations: `ROOTS.txt`. Historical 31-module logs
are not evidence for the subsequent covariance and Hessian additions.

| Manuscript obligation | Owned Lean coverage | Remaining mathematical obligation |
| --- | --- | --- |
| Actual Gaussian definitions and first moments | `GaussianPartition`: integrability, zero mean, fractional moments | Complete final measurable-set/AE adapters in the sharp theorem |
| Balanced prices and actual masses | `GaussianBalancedPrices`, `GaussianUniquePrices` | Handle all limiting configurations required by the global argument |
| Price primal-dual equality | `GaussianPrimalDual`, `GaussianFractionalEquality` | Derive tetrahedral optimality rather than merely assignment optimality |
| Covariance law, continuity, scaling (Lemma 2) | Integrated `GaussianCovarianceValue`, `GaussianCovarianceContinuity`, `GaussianValueScaling` | Higher positive-cone regularity |
| Actual flux and differential (Lemma 3) | Integrated flux modules and `FixedCovarianceDifferential` construct one fixed flux family for every centered direction | Upgrade the directional formula to required covariance smoothness; identify full geometric facet perimeter inputs |
| Uniform moment separation (Lemma 4) | `ScalarTent`, `SeparatedMoments`, `WinningSeparation` | No gap in the stated separation theorem |
| Price estimate (10) | `PriceBounds`, `PriceCompactness` | Moving-facet convergence is separate |
| Boundary continuity (Lemma 5) | `GaussianWinningContinuity`, `BoundarySeparation`, `TripleTie` | Gaussian surface-integral limits at singular diagrams |
| Rank-one/rank-two obstruction (Lemma 6) | `Profile`, `QuartileIntervals`, `OrderedWinning`, `RankOne`, `CollinearTransport`, `RankOneBridge` | Rank-one bridge is closed for injective score families, including relabeling and actual winning-cell transport; all rank-two hull cases; geometric isoperimetry and merged-cell bound remain open |
| Actual price Hessian | `PriceMassDifferential`, `PriceSecondVariation`, `PriceFrechetIntegral`, `PriceFrechetTransport`, `PriceHessian` | Joint parameter continuity and the smooth implicit price map |
| Gauge-fixed price nondegeneracy | `CenteredPriceHessian` constructs the centered operator and proves bijectivity | Uniform quantitative control required along deformations |
| Tetrahedral value and covariance Hessian (Lemma 7) | Generic simplex-value and algebra infrastructure | Exact arctangent evaluation; actual covariance second variation and strict local maximum |
| Full-rank criticality (Lemma 8) | `CovarianceCriticality`, `SelfMomentCriticality`: actual masses, positive multiplier, m_i=C(Q)r_i, L=C(Q)P | Actual four-cell perimeter lower bound and critical-value comparison |
| Constrained mountain pass (Lemma 9) | No complete owned deformation theorem | Construct the flow/deformation and minimax argument |
| Upper normals (20), residual (21) | `TraceSupport`, `NormalCone`, `RegularizedResidual` | Apply intrinsic matrices to regularized Gaussian critical sequences and singular limits |
| Global covariance comparison (Theorem 10) | Not exported | Assemble regularity, deformation, boundary exclusions and geometric inputs |
| Arbitrary partitions and full equality (Theorem 1) | Only actual moment/price and fractional-assignment infrastructure | Sharp comparison, full AE tetrahedral rigidity, relabeling, orthogonal and cylindrical equivalence |

The price Hessian and covariance Hessian are different mathematical objects.
Proving the former, including its centered inverse, does not prove the latter
or the global energy inequality. See `GAPS.md` for exact remaining statements.
No unavailable analytic or geometric theorem is an axiom of this project.

## Intrinsic boundary continuation

The new chain is MaskedTail -> PairSlice -> PairSliceIntegral ->
PairMassDerivative -> IntrinsicWeights -> IntrinsicContinuity ->
IntrinsicFlux -> IntrinsicBoundary. The existing WinningLimits source is
integrated byte-identically from 971408e7. See BOUNDARY_PROVENANCE.json.
This closes positive-chart compatibility via actual mass derivatives and
passes masses, Bochner flux and the entire Laplacian to distinct-score
balanced simplicial limits. It does not construct the variational sequence
or prove its rank exclusions or the geometric perimeter inputs.
The expanded inventory has 108 modules and 638 roots. The rank-one bridge is included in the fresh source-bound
verification receipts establish the current build/replay status.
