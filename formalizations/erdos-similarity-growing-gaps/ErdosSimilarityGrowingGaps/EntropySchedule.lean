import ErdosSimilarityGrowingGaps.GeometryChain
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
Noncircular output-window scheduling for a FIXED finite routing tree.
The template owner supplies fixed natural affine span coefficients A,B.
The schedule is chosen as an explicit logarithmic function of the absolute
output position U; arbitrarily late U satisfy both span and entropy budgets.
No power-remainder duty is introduced for the exact geometric target.
-/
namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

noncomputable def scheduledWindow (κ C : ℝ) (Lmin U : ℕ) : ℕ :=
  Lmin + Nat.ceil ((4 * Real.log ((U : ℝ) + 2) + max C 0) / κ)

theorem scheduledWindow_ge (κ C : ℝ) (Lmin U : ℕ) :
    Lmin ≤ scheduledWindow κ C Lmin U := Nat.le_add_right _ _

theorem scheduledWindow_log_lower (κ C : ℝ) (hκ : 0 < κ) (Lmin U : ℕ) :
    4 * Real.log ((U : ℝ) + 2) + C ≤ κ * (scheduledWindow κ C Lmin U : ℝ) := by
  have hceil := Nat.le_ceil ((4 * Real.log ((U : ℝ) + 2) + max C 0) / κ)
  have hm := (div_le_iff₀ hκ).1 hceil
  have hL : 0 ≤ (Lmin : ℝ) := Nat.cast_nonneg _
  have hC : C ≤ max C 0 := le_max_left _ _
  unfold scheduledWindow
  push_cast
  nlinarith

theorem scheduledWindow_real_upper (κ C : ℝ) (hκ : 0 < κ) (Lmin U : ℕ) :
    (scheduledWindow κ C Lmin U : ℝ) ≤
      (Lmin : ℝ) + (4 * Real.log ((U : ℝ) + 2) + max C 0) / κ + 1 := by
  have hlog : 0 ≤ Real.log ((U : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) U; linarith)
  have hf : 0 ≤ (4 * Real.log ((U : ℝ) + 2) + max C 0) / κ :=
    div_nonneg (by positivity) hκ.le
  have hceil := Nat.ceil_lt_add_one hf
  unfold scheduledWindow
  push_cast
  linarith

theorem tendsto_shifted_log_div_id :
    Tendsto (fun x : ℝ => Real.log (x + 2) / x) atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℝ => x + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_id
  have ht := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-2) 1 one_ne_zero).comp hshift
  simpa [Function.comp_def] using ht

/-- Every fixed affine template span fits inside U for all sufficiently late U. -/
theorem scheduledWindow_affine_span_eventually (κ C : ℝ) (hκ : 0 < κ)
    (A B Lmin : ℕ) :
    ∀ᶠ U : ℕ in atTop, A * scheduledWindow κ C Lmin U + B ≤ U := by
  let c : ℝ := (A : ℝ) * ((Lmin : ℝ) + max C 0 / κ + 1) + B
  have hc : Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) :=
    (isLittleO_const_id_atTop c).tendsto_div_nhds_zero
  have ht : Tendsto (fun x : ℝ =>
      ((4 * (A : ℝ) / κ) * Real.log (x + 2) + c) / x) atTop (𝓝 0) := by
    convert (tendsto_shifted_log_div_id.const_mul (4 * (A : ℝ) / κ)).add hc using 1
    · ext x
      ring
    · norm_num
  have he :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun U : ℕ => (U : ℝ)) atTop atTop).eventually
      (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with U hbound hU
  have hUr : (0 : ℝ) < U := by exact_mod_cast hU
  have hbig : (4 * (A : ℝ) / κ) * Real.log ((U : ℝ) + 2) + c < (U : ℝ) :=
    by simpa using (div_lt_iff₀ hUr).1 hbound
  have hupper := mul_le_mul_of_nonneg_left
    (scheduledWindow_real_upper κ C hκ Lmin U) (Nat.cast_nonneg A : (0 : ℝ) ≤ A)
  have hspan : (A : ℝ) * (scheduledWindow κ C Lmin U : ℝ) + B ≤ (U : ℝ) := by
    dsimp [c] at hbig
    have hid : (A : ℝ) * ((Lmin : ℝ) +
        (4 * Real.log ((U : ℝ) + 2) + max C 0) / κ + 1) + B =
        (4 * (A : ℝ) / κ) * Real.log ((U : ℝ) + 2) +
          ((A : ℝ) * ((Lmin : ℝ) + max C 0 / κ + 1) + B) := by ring
    linarith
  exact_mod_cast hspan

/-- Strict entropy decay follows from the logarithmic lower bound, including U=0. -/
theorem entropy_budget_of_log_lower (C₀ p κ L : ℝ) (hC₀ : 0 < C₀) (hp : 0 < p)
    (U : ℕ)
    (hlower : 4 * Real.log ((U : ℝ) + 2) + Real.log (C₀ / p) + 1 ≤ κ * L) :
    C₀ * ((U : ℝ) + 1) ^ 2 * Real.exp (-κ * L) < p := by
  have hU₁ : 0 < (U : ℝ) + 1 := by positivity
  have hcost : 0 < C₀ * ((U : ℝ) + 1) ^ 2 * Real.exp (-κ * L) := by positivity
  apply (Real.log_lt_log_iff hcost hp).1
  rw [Real.log_mul (mul_pos hC₀ (pow_pos hU₁ 2)).ne' (Real.exp_pos _).ne',
    Real.log_mul hC₀.ne' (pow_pos hU₁ 2).ne', Real.log_pow, Real.log_exp]
  rw [Real.log_div hC₀.ne' hp.ne'] at hlower
  have hmono : Real.log ((U : ℝ) + 1) ≤ Real.log ((U : ℝ) + 2) :=
    Real.log_le_log hU₁ (by linarith)
  have hnonneg : 0 ≤ Real.log ((U : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) U; linarith)
  norm_num only [Nat.cast_ofNat]
  nlinarith

/-- Arbitrarily late absolute positions satisfy the explicit schedule and strict budget. -/
theorem exists_late_entropy_schedule (C₀ p κ : ℝ) (hC₀ : 0 < C₀) (hp : 0 < p)
    (hκ : 0 < κ) (A B Lmin Umin : ℕ) :
    ∃ U L : ℕ, Umin ≤ U ∧ Lmin ≤ L ∧ A * L + B ≤ U ∧
      C₀ * ((U : ℝ) + 1) ^ 2 * Real.exp (-κ * (L : ℝ)) < p := by
  let C := Real.log (C₀ / p) + 1
  have hev := scheduledWindow_affine_span_eventually κ C hκ A B Lmin
  obtain ⟨U, hspan, hlate⟩ := (hev.and (eventually_ge_atTop Umin)).exists
  refine ⟨U, scheduledWindow κ C Lmin U, hlate, scheduledWindow_ge κ C Lmin U, hspan, ?_⟩
  exact entropy_budget_of_log_lower C₀ p κ _ hC₀ hp U
    (by simpa [C, add_assoc] using scheduledWindow_log_lower κ C hκ Lmin U)

end ErdosSimilarityGrowingGaps
