import Lake
open Lake DSL
package gaussianFourGlobalProgress where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "d13f23b723b8a846827a245b89c10fc7d3f11612"

-- Reuse the existing actual-measure sources, without changing or vendoring them.
lean_lib GaussianMeasureBridgeReuse where
  srcDir := "../gaussian-measure-primal-dual"
  roots := #[
    `GaussianPartition,
    `GaussianPrices,
    `GaussianNoTies,
    `GaussianFullSupport,
    `GaussianBalancedPrices,
    `GaussianWinningPartition,
    `GaussianUniquePrices,
    `GaussianPrimalDual,
    `GaussianFractionalEquality]

@[default_target]
lean_lib GaussianFourGlobalProgress where
  roots := #[
    `GaussianTent,
    `GaussianMomentSeparation,
    `GaussianWinningLimits,
    `GaussianBoundaryTransfer,
    `GaussianBalancedValue,
    `GaussianHomogeneity,
    `GaussianFractionalReduction,
    `GaussianSetPartitions,
    `GaussianGramInvariance,
    `GaussianEqualityGuard,
    `GaussianFourProgress,
    `UnprovedTargets]
