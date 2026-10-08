import ContinuumGeometric
open ContinuumGeometric
example : periodicGridKey 4 (1 / 4) = 0 := by
  norm_num [periodicGridKey]
