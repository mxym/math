import HypothesisMutations
open Set IndependentRemainderControls
example : (1:ℝ)+1 ∈ Metric.thickening 2 ({0}:Set ℝ) := by
  have h := closed_inner_buffer_breaks_outer.2.2
  simp_all
  norm_num at *
