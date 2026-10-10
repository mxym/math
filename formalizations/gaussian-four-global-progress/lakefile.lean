import Lake
open Lake DSL

package gaussianFourGlobalProgress

require gaussianMeasureBridge from "../gaussian-measure-primal-dual"

@[default_target]
lean_lib GaussianFour where
  roots := #[`GaussianFour]
