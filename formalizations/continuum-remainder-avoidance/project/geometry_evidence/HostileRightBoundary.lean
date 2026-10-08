import ContinuumGeometric.RoutingGeometry
open ContinuumGeometric
example : periodicGridKey 8 (1 / 8 : ℝ) = periodicGridKey 8 0 := by
  norm_num [periodicGridKey]
