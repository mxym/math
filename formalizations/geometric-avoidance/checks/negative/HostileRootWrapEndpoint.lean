import ContinuumGeometric.PeriodicRepair
open ContinuumGeometric
-- Deliberately false: zero is outside the preceding half-open wrapped cell.
example : periodicGridKey 32 (-1 / 32) = periodicGridKey 32 0 := by
  norm_num [periodicGridKey]
