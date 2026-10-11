import ErdosSimilarityGrowingGaps.HerrorActivation

namespace ErdosSimilarityGrowingGaps

/-! The finest-grid buffer comparison in the shifted-exponent form used by
the global-window herror bridge. -/
theorem herror_buffer_compare_bridge
    (p q X C : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (hC : q * (2 : ℝ) ^ (-C) < p / 32) :
    q * (2 : ℝ) ^ (-(X + C)) <
      p / (8 * (2 : ℝ) ^ (X + 2)) := by
  have hpowX : 0 < (2 : ℝ) ^ (-X) := Real.rpow_pos_of_pos (by norm_num) _
  have hleft : q * (2 : ℝ) ^ (-(X + C)) =
      q * (2 : ℝ) ^ (-C) * (2 : ℝ) ^ (-X) := by
    rw [show -(X + C) = (-C) + (-X) by ring,
      Real.rpow_add (by norm_num)]
    ring
  have hright : p / (8 * (2 : ℝ) ^ (X + 2)) =
      (p / 32) * (2 : ℝ) ^ (-X) := by
    rw [show X + 2 = X + (2 : ℝ) by ring,
      Real.rpow_add (by norm_num)]
    norm_num [Real.rpow_natCast]
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
    norm_num
  rw [hleft, hright]
  exact mul_lt_mul_of_pos_right hC hpowX

end ErdosSimilarityGrowingGaps
