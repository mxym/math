import Entry005
open Entry005
example : thresholdGateGoal := thresholdGate
example : aSharp 2 * (eSharp 2) ^ (1 / ((2 - 1 : ℕ) : ℝ)) ≤ 1 / 2 :=
  aSharp_mul_eSharp_root_le_half (by norm_num)
example : aSharp 3 * (0 : ℝ) ^ (1 / ((3 - 1 : ℕ) : ℝ)) ≤ 1 / 2 :=
  small_defect_gate (by norm_num) (by norm_num) (eSharp_pos (by norm_num)).le
example : aSharp 3 * (eSharp 3) ^ (1 / ((3 - 1 : ℕ) : ℝ)) ≤ 1 / 2 :=
  small_defect_gate (by norm_num) (eSharp_pos (by norm_num)).le le_rfl
