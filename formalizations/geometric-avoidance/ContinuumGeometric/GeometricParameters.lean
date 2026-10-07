import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace ContinuumGeometric

open Filter Topology

noncomputable def dyadic (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

/-- Exact equality for every index, not approximation of a real exponent. -/
theorem dyadic_power_eq (s : ℝ) (n : ℕ) :
    (dyadic n) ^ s = ((1 / 2 : ℝ) ^ s) ^ n := by
  unfold dyadic
  calc
    ((1 / 2 : ℝ) ^ n) ^ s = (1 / 2 : ℝ) ^ ((n : ℝ) * s) :=
      (Real.rpow_natCast_mul (by norm_num) n s).symm
    _ = (1 / 2 : ℝ) ^ (s * (n : ℝ)) := by rw [mul_comm]
    _ = ((1 / 2 : ℝ) ^ s) ^ n := Real.rpow_mul_natCast (by norm_num) s n

/-- The entire continuum of ratios is parametrized by positive real powers. -/
theorem geometric_parameter (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    ∃ s : ℝ, 0 < s ∧ ∀ n : ℕ, q ^ n = (dyadic n) ^ s := by
  refine ⟨Real.logb (1 / 2) q, ?_, ?_⟩
  · exact Real.logb_pos_of_base_lt_one (by norm_num) (by norm_num) hq₀ hq₁
  · intro n
    rw [dyadic_power_eq, Real.rpow_logb (by norm_num) (by norm_num) hq₀]

/-- The limit used for repairing exceptional centers; it allows either sign of `a`. -/
theorem affine_geometric_tendsto (a b q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    Tendsto (fun n : ℕ => a * q ^ n + b) atTop (𝓝 b) := by
  simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq₀.le hq₁).const_mul a).add_const b

/-- A neighborhood of the limiting center hits every geometric tail. -/
theorem every_tail_hits_open (V : Set ℝ) (hV : IsOpen V)
    (a b q : ℝ) (hb : b ∈ V) (hq₀ : 0 < q) (hq₁ : q < 1) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ a * q ^ n + b ∈ V := by
  have hev : ∀ᶠ n : ℕ in atTop, a * q ^ n + b ∈ V :=
    (affine_geometric_tendsto a b q hq₀ hq₁).eventually (hV.mem_nhds hb)
  rcases (eventually_atTop.1 hev) with ⟨K, hK⟩
  exact ⟨max N K, le_max_left _ _, hK _ (le_max_right _ _)⟩

end ContinuumGeometric
