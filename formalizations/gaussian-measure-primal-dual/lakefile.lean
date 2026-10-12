import Lake
open Lake DSL

package gaussianMeasureBridge

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "d13f23b723b8a846827a245b89c10fc7d3f11612"

lean_lib GaussianMeasureBridge where
  roots := #[`GaussianPartition, `GaussianPrices, `GaussianNoTies,
    `GaussianFullSupport, `GaussianBalancedPrices, `GaussianWinningPartition,
    `GaussianUniquePrices, `GaussianPrimalDual, `GaussianFractionalEquality]
