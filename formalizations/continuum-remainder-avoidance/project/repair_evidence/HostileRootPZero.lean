import ContinuumGeometric.RoutingSchedule
open ContinuumGeometric
-- Deliberately false: the P=0 entropy cost is 500, not zero.
example : 20 * ((0 : ℝ) * (3 + (2 : ℝ) ^ 3) + 5) ^ 2 = 0 := by norm_num
