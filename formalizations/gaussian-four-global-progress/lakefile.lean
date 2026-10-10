import Lake
open Lake DSL

package gaussianFourGlobalProgress

require gaussianMeasureBridge from "../gaussian-measure-primal-dual"

lean_lib GaussianFourProfileSupport where
  srcDir := "../gaussian-mass-envelope-progress"
  roots := #[`GaussianHalflineFlux, `GaussianHalfspaceFlux, `GaussianTail,
    `GaussianHazard, `GaussianQuantile, `GaussianOneCell]

@[default_target]
lean_lib GaussianFour where
  roots := #[`GaussianFour]
