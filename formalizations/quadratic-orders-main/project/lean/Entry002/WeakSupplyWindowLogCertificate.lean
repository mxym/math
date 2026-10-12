import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Exact rational bounds for the logarithm used by the finite window cover. -/

namespace Entry002

open scoped BigOperators

theorem weakSupplyWindow_log100_eq :
    Real.log (100 : ℝ) = 6 * Real.log (2 : ℝ) + 2 * Real.log (5 / 4 : ℝ) := by
  have h100 : (100 : ℝ) = 2 ^ 6 * (5 / 4) ^ 2 := by norm_num
  rw [h100, Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  norm_num

/-- A rational partial-sum certificate, including a proved remainder bound. -/
theorem weakSupplyWindow_log100_bounds :
    (4605 / 1000 : ℝ) ≤ Real.log (100 : ℝ) ∧
      Real.log (100 : ℝ) ≤ (4606 / 1000 : ℝ) := by
  have hlo2 := Real.sum_range_le_log_div (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 4
  have hhi2 := Real.log_div_le_sum_range_add (x := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) 4
  have hlo54 := Real.sum_range_le_log_div (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 2
  have hhi54 := Real.log_div_le_sum_range_add (x := (1 / 9 : ℝ))
    (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at hlo2 hhi2 hlo54 hhi54
  rw [weakSupplyWindow_log100_eq]
  constructor <;> linarith

end Entry002
