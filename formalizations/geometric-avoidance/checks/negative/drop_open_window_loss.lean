import ContinuumGeometric
open ContinuumGeometric
example : (8 : ℝ) ≤ ((activeIntegers 8 16 2).card : ℝ) := by
  rw [activation_card_exact 8 16 2 (by norm_num) (by norm_num)]
  norm_num
