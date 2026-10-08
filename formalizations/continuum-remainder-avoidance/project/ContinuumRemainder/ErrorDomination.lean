import ContinuumGeometric.ZeroErrorBuffer
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
The actual section 6 active-point error estimate.  The radius is positive
even for q = 0.  Its extra +1 gives strict room; the perturbation lemma also
accepts the closed endpoint |e| = r, because the inner buffer is open.
-/
namespace ContinuumRemainder

noncomputable def errorRadius (q : ℕ) (k : ℤ) (α₀ s₁ U : ℝ) : ℝ :=
  ((q : ℝ) * (2 : ℝ) ^ (-k) + 1) * (2 : ℝ) ^ (-U) *
    (2 : ℝ) ^ (-α₀ * (U + (k : ℝ)) / s₁)

theorem errorRadius_pos (q : ℕ) (k : ℤ) (α₀ s₁ U : ℝ) :
    0 < errorRadius q k α₀ s₁ U := by
  unfold errorRadius
  positivity

/-- Activation gives the input logarithm lower bound, including U+k=0. -/
theorem active_log_lower (z s s₁ U : ℝ) (k : ℤ)
    (hs : 0 < s) (hss₁ : s ≤ s₁) (hUk : 0 ≤ U + (k : ℝ))
    (hactive : U < s * z - k) :
    0 < z ∧ (U + (k : ℝ)) / s₁ < z := by
  have hs₁ : 0 < s₁ := hs.trans_le hss₁
  have hsz : 0 < s * z := by linarith
  have hz : 0 < z := (mul_pos_iff_of_pos_left hs).1 hsz
  refine ⟨hz, (div_lt_iff₀ hs₁).2 ?_⟩
  have hmul := mul_le_mul_of_nonneg_right hss₁ hz.le
  nlinarith

/-- Every actually active input has an error smaller than the common radius. -/
theorem active_power_error_lt_radius (q : ℕ) (k : ℤ) (a z s s₁ α₀ U : ℝ)
    (ha : a = (2 : ℝ) ^ (-z)) (hs : 0 < s) (hss₁ : s ≤ s₁)
    (hα : 0 < α₀) (hUk : 0 ≤ U + (k : ℝ))
    (hactive : U < s * z - k) :
    (q : ℝ) * a ^ (s + α₀) < errorRadius q k α₀ s₁ U := by
  have hs₁ : 0 < s₁ := hs.trans_le hss₁
  obtain ⟨hz, hzl⟩ := active_log_lower z s s₁ U k hs hss₁ hUk hactive
  have hαz : α₀ * ((U + (k : ℝ)) / s₁) ≤ α₀ * z :=
    mul_le_mul_of_nonneg_left hzl.le hα.le
  have hexp : -z * (s + α₀) ≤ -(k : ℝ) - U +
      (-α₀ * (U + (k : ℝ)) / s₁) := by
    have hdiv : α₀ * ((U + (k : ℝ)) / s₁) =
        α₀ * (U + (k : ℝ)) / s₁ := by ring
    rw [hdiv] at hαz
    rw [show -α₀ * (U + (k : ℝ)) / s₁ =
      -(α₀ * (U + (k : ℝ)) / s₁) by ring]
    nlinarith
  have hpower : a ^ (s + α₀) ≤ (2 : ℝ) ^ (-k) *
      (2 : ℝ) ^ (-U) * (2 : ℝ) ^ (-α₀ * (U + (k : ℝ)) / s₁) := by
    rw [ha, ← Real.rpow_mul (by norm_num)]
    calc
      (2 : ℝ) ^ (-z * (s + α₀)) ≤
          (2 : ℝ) ^ (-(k : ℝ) - U + (-α₀ * (U + (k : ℝ)) / s₁)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = _ := by
        rw [Real.rpow_add (by norm_num), sub_eq_add_neg,
          Real.rpow_add (by norm_num), ← Int.cast_neg, Real.rpow_intCast]
  have hq := mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hpos : 0 < (2 : ℝ) ^ (-U) *
      (2 : ℝ) ^ (-α₀ * (U + (k : ℝ)) / s₁) := by positivity
  unfold errorRadius
  nlinarith

theorem active_power_error_le_radius (q : ℕ) (k : ℤ) (a z s s₁ α₀ U : ℝ)
    (ha : a = (2 : ℝ) ^ (-z)) (hs : 0 < s) (hss₁ : s ≤ s₁)
    (hα : 0 < α₀) (hUk : 0 ≤ U + (k : ℝ))
    (hactive : U < s * z - k) :
    (q : ℝ) * a ^ (s + α₀) ≤ errorRadius q k α₀ s₁ U :=
  (active_power_error_lt_radius q k a z s s₁ α₀ U ha hs hss₁ hα hUk hactive).le

/-- The actual allowed error, of either sign, lands in the outer open buffer. -/
theorem active_error_in_outer_buffer (B : Set ℝ) (q : ℕ) (k : ℤ)
    (a z s s₁ α₀ U x t e : ℝ)
    (ha : a = (2 : ℝ) ^ (-z)) (hs : 0 < s) (hss₁ : s ≤ s₁)
    (hα : 0 < α₀) (hUk : 0 ≤ U + (k : ℝ))
    (hactive : U < s * z - k)
    (hhit : x + t * (2 : ℝ) ^ k * a ^ s ∈
      Metric.thickening (errorRadius q k α₀ s₁ U) B)
    (he : |e| ≤ (q : ℝ) * a ^ (s + α₀)) :
    x + t * (2 : ℝ) ^ k * a ^ s + e ∈
      Metric.thickening (2 * errorRadius q k α₀ s₁ U) B := by
  exact ContinuumGeometric.double_buffer_contains_perturbation B _ _ _ hhit
    (he.trans (active_power_error_le_radius q k a z s s₁ α₀ U
      ha hs hss₁ hα hUk hactive))

end ContinuumRemainder
