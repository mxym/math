# Four-cell global theorem: proof-to-Lean correspondence

Status: partial formalization. This is not a proof of Theorem 1 or Theorem 10.

Baseline main: `0071871`. Manuscript: `research/gaussian-balanced-four-global/paper.md`.
The all-k source directory is absent from this main baseline. Its actual reusable
source is on `research/gaussian-three-cell-20261008`, fixed at
`da16f54190bb53651a78640bd94a30a5c2cc9e08`. A branch-local proof must not be
misrepresented as already imported by this package or as freshly reverified.

| Paper obligation | Actual existing Lean | Exact remaining obligation |
|---|---|---|
| Definitions; integrability; zero mean | Main `GaussianPartition`: `integrable_weighted_id`, `sum_moment`, `inner_moment` | No Gaussian-property assumptions are needed. Measurable-set adaptation must retain AE partition constraints. |
| Balanced prices, actual masses | Main `GaussianBalancedPrices.exists_balancing_prices`; `GaussianUniquePrices.balancing_prices_unique_mod_const` | These cover arbitrary positive masses and distinct scores. Tied scores need only the dual minimizer in this manuscript. |
| Assignment dual and fractional equality | Main `GaussianPrimalDual.actual_gaussian_primal_dual`; `GaussianFractionalEquality.fractional_dual_equality_ae_winning` | Geometric optimality and regularity do not follow from these alone. |
| Lemma 2: actual covariance law, continuity, scaling | Research branch `GaussianCovarianceValue`, `GaussianCovarianceContinuity` | Reviewed types cover singular PSD matrices and changes of ambient dimension. Not newly proved here. |
| Lemma 3: flux and covariance derivative | Research branch `GaussianAllCellsFlux`, `GaussianCovarianceDifferential`, `GaussianFacetLaplacian` and dependencies | Need exact integration into the four-cell positive cone; smoothness of higher derivatives/local Hessian is separate. |
| Lemma 4: uniform separation | `GaussianFour.ScalarTent`, `SeparatedMoments`, `WinningSeparation` | Prove actual Gaussian two-label separation with original constant, not a sampled or assumed density model. |
| Equation (10): price bound | Positive-mass halfspace constraints available | Exact Gaussian quantile price-difference bound still required for this route. |
| Lemma 5: boundary convergence | Research branch `GaussianWinningContinuity.continuousAt_rawWinningMoment` | Moment continuity alone does not prove facet-area continuity. Triple-tie exclusion and moving-hyperplane integral limit remain. |
| Lemma 6: singular self-moment obstruction | Research branch three-score width and three-cell bound; main scalar algebra diagnostics | Rank-two affine dependence/hull cases, single-cell isoperimetry with actual perimeter, and the covariance-to-facet bridge remain. The quantile margin and ordered collinear facet computation are now proved in `Profile`, `RankOne`, and `CollinearTransport`. A three-cell equal-mass endpoint alone is insufficient for merged cells. |
| Lemma 7: tetrahedral value and strict local maximum | Research branch regular-simplex attainment in terms of `simplexConstant` | Exact arctangent evaluation and actual second variation yielding formula (16) remain. |
| Lemma 8: full-rank critical lower bound | Research branch covariance/perimeter algebra and conditional comparison | Four-cell Gaussian perimeter minimum is NOT proved merely by this reduction. |
| Lemma 9: constrained mountain pass | No matching completed module found in the research source inventory | Actual compact-convex deformation with upper-normal sign; no postulated ODE or deformation map. |
| Theorem 10: covariance global maximum | Scalar residual diagnostics in old four-cell package | Matrix normal-cone/top-eigenspace equivalence, residual estimate, subsequence compactness, boundary exclusions, and global contradiction must be assembled. |
| Theorem 1: all measurable/fractional partitions | Main price dual; research branch moment covariance/equality transport | Still depends on the unproved sharp covariance comparison; cannot export a conditional wrapper as the target theorem. |
| Complete equality classification | Research branch Gram isometry and fractional winning-label equality | Must prove the sharp equality covariance and exact tetrahedral constant, then AE/orthogonal/relabeling/cylindrical equivalence without extra geometric assumptions. |

## External geometric obligations

The manuscript imports Milman–Neeman's Gaussian multi-bubble theorem and the
single-cell Gaussian isoperimetric theorem. No custom axiom is introduced for
either. Neither is established by this package. A manuscript citation is not a
Lean proof. The research branch's `EqualMassSimplicialPerimeterBound` and BV
compactness interfaces are explicitly supplied propositions, not unconditional
solutions of these obligations.

The full all-k radial route is an alternative to the four-cell mountain-pass
route, but it also requires a sharp perimeter lower bound. Unconditionally
proving an upper BV/erosion bridge or constructing a bounded minimizing sequence
does not prove that lower bound, compactness, or minimizer geometry.

## Publication discipline

Existing immutable manuscript editions are untouched. Development takes place
on a separate branch. No complete-formalization release is justified until the
actual partition inequality and all equality directions are unconditional.

## Current additions

The new analytic chain is `Profile -> QuartileIntervals -> OrderedWinning -> RankOne -> CollinearTransport`. All use actual Gaussian measures and moments. See `PROOF.md` and `GAPS.md` for exact scope and remaining statements. All 26 modules and 206 declared audit roots are included in fresh compilation and trust-zero replay.
