import Mathlib.Tactic
-- Deliberately false: removing the merge constraint destroys the bound.
example : (6 : ℚ)+4*1 ≤ 4*1/3 := by norm_num
