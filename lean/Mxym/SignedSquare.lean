import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The elementary scalar mechanism in entry001 v5 (eq:signed-square)
and entry008 v1, Section 2. No transport or integration theorem is assumed. -/
namespace Mxym.Transport

theorem signed_square (a b : ℝ) (hab : a ≤ b) :
    (b - a) ^ 2 ≤ 2 * (b * |b| - a * |a|) := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := le_trans ha hab
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    nlinarith [sq_nonneg (b - a), mul_nonneg ha (sub_nonneg.mpr hab)]
  · by_cases hb : b ≤ 0
    · rw [abs_of_nonpos (le_of_lt (lt_of_not_ge ha)), abs_of_nonpos hb]
      nlinarith [mul_nonneg (neg_nonneg.mpr hb) (sub_nonneg.mpr hab)]
    · rw [abs_of_nonpos (le_of_lt (lt_of_not_ge ha)),
        abs_of_nonneg (le_of_lt (lt_of_not_ge hb))]
      nlinarith [sq_nonneg (a + b)]

theorem signed_square_eq_iff (a b : ℝ) (hab : a ≤ b) :
    (b - a) ^ 2 = 2 * (b * |b| - a * |a|) ↔ a = b ∨ a = -b := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := le_trans ha hab
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    constructor
    · intro h
      have hprod : (b - a) * (b + 3 * a) = 0 := by nlinarith [h]
      rcases mul_eq_zero.mp hprod with h | h
      · left; linarith
      · left; nlinarith
    · rintro (h | h) <;> nlinarith
  · by_cases hb : b ≤ 0
    · rw [abs_of_nonpos (le_of_lt (lt_of_not_ge ha)), abs_of_nonpos hb]
      constructor
      · intro h
        have hprod : (b - a) * (3 * b + a) = 0 := by nlinarith [h]
        rcases mul_eq_zero.mp hprod with h | h
        · left; linarith
        · left; nlinarith
      · rintro (h | h) <;> nlinarith
    · rw [abs_of_nonpos (le_of_lt (lt_of_not_ge ha)),
        abs_of_nonneg (le_of_lt (lt_of_not_ge hb))]
      constructor
      · intro h
        right
        have hsq : (a + b) ^ 2 = 0 := by nlinarith [h]
        have := (sq_eq_zero_iff).mp hsq
        linarith
      · rintro (h | h) <;> nlinarith

theorem intermediate_square (a q b : ℝ) (haq : a ≤ q) (hqb : q ≤ b) :
    (q - a) ^ 2 ≤ 2 * (b * |b| - a * |a|) := by
  have hab := le_trans haq hqb
  have hs := signed_square a b hab
  nlinarith [mul_nonneg (sub_nonneg.mpr hqb) (sub_nonneg.mpr haq)]

theorem three_term_square (x y z : ℝ) :
    (x + y + z) ^ 2 ≤ 3 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

end Mxym.Transport
