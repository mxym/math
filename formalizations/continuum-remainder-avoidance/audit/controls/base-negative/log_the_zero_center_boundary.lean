import ContinuumGeometric
open ContinuumGeometric
example : (0 : ℤ) ∈ liftedBoundaryBatch 4 0 (1 / 4) := by
  rw [mem_liftedBoundaryBatch_iff 4 (by norm_num)]
  norm_num
