import ContinuumGeometric
open ContinuumGeometric
example : 4 * (8 : ℝ) * (0 / (8 * 8)) < 0 := by
  norm_num
