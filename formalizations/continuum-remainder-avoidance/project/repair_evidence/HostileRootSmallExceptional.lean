import ContinuumGeometric.PeriodicRepair
open Set MeasureTheory ContinuumGeometric
open scoped ENNReal
-- Deliberately false: the actual exceptional density premise cannot be erased.
example : unitDensity (univ : Set ℝ) ≤ ENNReal.ofReal (1 / 100) := by
  norm_num [unitDensity, Real.volume_Ico]
