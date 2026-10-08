import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory

namespace Entry005

theorem radial_power_integrableOn (k : ℕ) (h : ℝ) :
    IntegrableOn (fun s : ℝ => (s / h) ^ k) (Set.Icc (0 : ℝ) h) volume :=
  ((continuous_id.div_const h).pow k).integrableOn_Icc

theorem radial_power_integral (k : ℕ) (h : ℝ) (hh : 0 < h) :
    (∫ s in Set.Icc (0 : ℝ) h, (s / h) ^ k ∂volume) = h / (k + 1 : ℝ) := by
  simp_rw [div_pow]
  rw [integral_div, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hh.le, integral_pow]
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  simp only [zero_pow (Nat.add_one_ne_zero k), sub_zero, pow_succ]
  field_simp [hh.ne', hk, pow_ne_zero k hh.ne']

end Entry005
