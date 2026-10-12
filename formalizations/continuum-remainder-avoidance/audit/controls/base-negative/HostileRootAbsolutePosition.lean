import ContinuumGeometric.RoutingSchedule
open ContinuumGeometric
-- Deliberately false: discarding the absolute origin loses actual candidates.
example : candidateLabelBudget 3000 0 0 ≤ candidateLabelBudget 0 0 0 := by
  norm_num [candidateLabelBudget]
