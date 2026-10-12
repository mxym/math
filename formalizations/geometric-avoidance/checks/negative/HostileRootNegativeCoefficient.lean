import ContinuumGeometric.RoutingSchedule
open ContinuumGeometric
-- Deliberately false: a negative k still incurs its absolute-position cost.
example : candidateLabelBudget 0 0 (-300) ≤ candidateLabelBudget 0 0 0 := by
  norm_num [candidateLabelBudget]
