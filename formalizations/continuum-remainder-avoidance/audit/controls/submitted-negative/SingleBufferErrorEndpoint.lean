import ContinuumRemainder.FinalProof
open Set ContinuumGeometric ContinuumRemainder
set_option autoImplicit false
example : (1/2 : ℝ)+1 ∈ Metric.thickening 1 ({0}:Set ℝ) := by
  apply Metric.mem_thickening_iff.2
  refine ⟨0, by simp, ?_⟩
  norm_num [Real.dist_eq]
