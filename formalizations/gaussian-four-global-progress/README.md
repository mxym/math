# 四胞高斯全局定理：部分形式化 / Partial formalization

This package advances the actual Gaussian analytic boundary argument. It does
**not** prove the global tetrahedral sharp bound or its equality classification.
It must not be described as a complete Lean formalization of that theorem.

## Current unconditional proof sources

- `GaussianTent.lean`: exact Lebesgue tent area and actual Gaussian projection bound.
- `GaussianMomentSeparation.lean`: actual fractional pair separation and the exact
  balanced winning-cell constant `1/(16*phi(0)) = sqrt(2*pi)/16`.
- `GaussianWinningLimits.lean`: convergence of actual integrals of every integrable
  function over moving winning cells, including masses and Bochner first moments.
- `GaussianBoundaryTransfer.lean`: actual residual convergence implies distinct
  limiting scores and a positive multiplier, then a balanced self-moment limit.

The residual-convergence hypotheses are explicit. The covariance/spectral
argument producing them is not included. Facet-area continuity is not included.
The results hold in every finite dimension when their stated hypotheses hold;
no full-rank assumption is hidden in the limiting lemmas.

The nine actual-measure sources in `../gaussian-measure-primal-dual` are reused
without source changes. Their theorems concern Mathlib `stdGaussian`, actual
measurable fractional labels and Bochner moments, not an abstract Gaussian axiom
package. See `COVERAGE.md` for the theorem-to-proof correspondence and gaps.

## Verification checkpoint

The four sources above have each passed Lean 4.34.1 compilation, against
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. A new clean Lake build,
empty-kernel replay, mutation checks and independently retained logs are being
assembled; no previous package log is claimed as a new verification of these
sources. This checkpoint is not an immutable release and is not merged into main.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. No external funding. AI-assisted research.
Original new materials: all rights reserved unless separately licensed.
Existing source licenses and third-party notices remain unchanged.
