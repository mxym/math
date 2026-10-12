import ContinuumGeometric.Planar
open ContinuumGeometric
-- Intentionally false: the boundary zero must not become positive.
example : cutSign (evalCut (1,0,0) (0,0)) = .positive := by
  norm_num [evalCut, cutSign]
