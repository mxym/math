import Entry002.WeakCoreFiniteSieveSupport

/-! Literal common-window rates compared with the harmonic good-bin weights.
No change is made to the actual sampling lengths or common law. -/
set_option autoImplicit false
namespace Entry002.WeakA5
open scoped BigOperators

/-- The actual rate dominates a fixed multiple of the supplied harmonic
weight in every positive dyadic bin. -/
theorem harmonic_weight_le_windowBatchRate {c : ℝ} (hc : 0 ≤ c)
    {j : ℕ} (hj : 0 < j) :
    (c / 10000000) * (1 / ((j : ℝ) + 1)) ≤ windowBatchRate c j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hlpos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlle : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hdenpos : 0 < 10000000 * ((j : ℝ) * Real.log 2) := by positivity
  have hden : 10000000 * ((j : ℝ) * Real.log 2) ≤ 10000000 * ((j : ℝ) + 1) := by
    nlinarith only [hlle, hjpos]
  have hh := div_le_div_of_nonneg_left hc hdenpos hden
  unfold windowBatchRate
  rw [Real.log_pow]
  simpa only [div_mul_div_comm, mul_one] using hh

end Entry002.WeakA5
