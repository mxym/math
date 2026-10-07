import ContinuumGeometric.RoutingSchedule
open ContinuumGeometric
-- Deliberately false: the squared candidate-position coefficient is required.
example : 20 * ((100 : ℝ) * (3 + (2 : ℝ) ^ 3) + 5) ^ 2 ≤ 5120 := by norm_num
