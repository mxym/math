import Entry005.Targets
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
The scalar threshold gate for the unchanged constants in `Entry005.Constants`.
No geometric assumption or local/main stability conclusion is used here.
-/

noncomputable section
set_option autoImplicit false

namespace Entry005

/-- A positive reciprocal-power threshold survives taking the positive root. -/
theorem root_bound_of_reciprocal_power {n : ℕ} (hn : n ≠ 0)
    {A J r : ℝ} (hA : 0 < A) (hJ : 0 < J) (hr : 0 ≤ r)
    (hbound : r ≤ 1 / (J * A ^ n)) :
    (J * r) ^ (1 / (n : ℝ)) ≤ 1 / A := by
  have hbase : J * r ≤ (A ^ n)⁻¹ := by
    calc
      J * r ≤ J * (1 / (J * A ^ n)) :=
        mul_le_mul_of_nonneg_left hbound hJ.le
      _ = (A ^ n)⁻¹ := by field_simp
  calc
    (J * r) ^ (1 / (n : ℝ)) ≤ ((A ^ n)⁻¹) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow (mul_nonneg hJ.le hr) hbase (by positivity)
    _ = 1 / A := by
      rw [Real.inv_rpow (by positivity), one_div,
        Real.pow_rpow_inv_natCast hA.le hn, one_div]

/-- The minimum in `rSharp` gives exactly the root bound needed by the local lane. -/
theorem rSharp_root_bound {d : ℕ} (hd : 2 ≤ d) :
    (J d * rSharp d) ^ (1 / ((d - 1 : ℕ) : ℝ)) ≤
      1 / (8 * M d * d * L d) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hM := M_pos hd1
  have hL := L_pos hd
  apply root_bound_of_reciprocal_power (by omega) (by positivity)
    (J_pos hd1) (rSharp_pos hd).le
  exact min_le_right _ _

/-- The literal threshold inequality, valid already in dimension two. -/
theorem aSharp_mul_eSharp_root_le_half {d : ℕ} (hd : 2 ≤ d) :
    aSharp d * (eSharp d) ^ (1 / ((d - 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
  have hd1 : 1 ≤ d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hM := M_pos hd1
  have hL := L_pos hd
  have hJ := J_pos hd1
  have hQ := Q_pos hd1
  have hr := rSharp_pos hd
  have hB : 0 < Q d * ((d : ℝ) + 1) := by positivity
  have hprod : J d * Q d * ((d : ℝ) + 1) *
      (rSharp d / (Q d * ((d : ℝ) + 1))) = J d * rSharp d := by
    field_simp
  calc
    aSharp d * (eSharp d) ^ (1 / ((d - 1 : ℕ) : ℝ)) =
        (4 * M d * d * L d) *
          (J d * rSharp d) ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
      unfold aSharp eSharp
      rw [mul_assoc, ← Real.mul_rpow (by positivity) (by positivity), hprod]
    _ ≤ (4 * M d * d * L d) * (1 / (8 * M d * d * L d)) :=
      mul_le_mul_of_nonneg_left (rSharp_root_bound hd) (by positivity)
    _ = 1 / 2 := by field_simp; ring

/-- An inhabitant of the unchanged target proposition. -/
theorem thresholdGate : thresholdGateGoal := by
  intro d hd
  exact aSharp_mul_eSharp_root_le_half (by omega)

/-- The defect threshold rescales to the actual minimum radius. -/
theorem scaled_defect_le_rSharp {d : ℕ} (hd : 2 ≤ d) {δ : ℝ}
    (hδ : δ ≤ eSharp d) : Q d * ((d : ℝ) + 1) * δ ≤ rSharp d := by
  have hQ := Q_pos (show 1 ≤ d by omega)
  have hB : 0 < Q d * ((d : ℝ) + 1) := by positivity
  have hscaled := (le_div_iff₀ hB).mp hδ
  simpa only [mul_comm δ] using hscaled

/-- The first branch of the minimum gives the small cap-radius threshold. -/
theorem scaled_defect_le_b {d : ℕ} (hd : 2 ≤ d) {δ : ℝ}
    (hδ : δ ≤ eSharp d) : Q d * ((d : ℝ) + 1) * δ ≤ b d := by
  exact (scaled_defect_le_rSharp hd hδ).trans (min_le_left _ _)

/-- The second branch gives the root threshold used by the geometric lane. -/
theorem scaled_defect_root_bound {d : ℕ} (hd : 2 ≤ d) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ eSharp d) :
    (J d * Q d * ((d : ℝ) + 1) * δ) ^ (1 / ((d - 1 : ℕ) : ℝ)) ≤
      1 / (8 * M d * d * L d) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hM := M_pos hd1
  have hL := L_pos hd
  have hQ := Q_pos hd1
  have hscaled := root_bound_of_reciprocal_power
    (show d - 1 ≠ 0 by omega)
    (show 0 < 8 * M d * d * L d by positivity) (J_pos hd1)
    (show 0 ≤ Q d * ((d : ℝ) + 1) * δ by positivity)
    ((scaled_defect_le_rSharp hd hδ).trans (min_le_right _ _))
  simpa only [mul_assoc] using hscaled

/-- Every nonnegative defect below `eSharp` satisfies the local half-size gate. -/
theorem small_defect_gate {d : ℕ} (hd : 2 ≤ d) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ eSharp d) :
    aSharp d * δ ^ (1 / ((d - 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
  calc
    aSharp d * δ ^ (1 / ((d - 1 : ℕ) : ℝ)) ≤
        aSharp d * (eSharp d) ^ (1 / ((d - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hδ0 hδ (by positivity))
        (aSharp_pos hd).le
    _ ≤ 1 / 2 := aSharp_mul_eSharp_root_le_half hd

end Entry005
