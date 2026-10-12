import ContinuumRemainder.ErrorDomination
import ContinuumGeometric.EntropySchedule
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
The coupled section 6 schedule.  The actual finest grid has 2^(U+T+2)
cells.  A fixed affine template span obtained from the original logarithmic
window schedule is sublinear, so its positive-error double-buffer cost tends
to zero.  The entropy and buffer budgets can therefore be met simultaneously
at arbitrarily late output positions; no radius is selected after freezing U.
-/
namespace ContinuumRemainder

open Filter Topology Asymptotics ContinuumGeometric

noncomputable def scheduledSpan (κ C : ℝ) (A B Lmin U : ℕ) : ℕ :=
  A * scheduledWindow κ C Lmin U + B

/-- An explicit logarithmic upper bound for the actual fixed-tree span. -/
theorem scheduledSpan_real_upper (κ C : ℝ) (hκ : 0 < κ) (A B Lmin U : ℕ) :
    (scheduledSpan κ C A B Lmin U : ℝ) ≤
      (4 * (A : ℝ) / κ) * Real.log ((U : ℝ) + 2) +
      ((A : ℝ) * ((Lmin : ℝ) + max C 0 / κ + 1) + B) := by
  have h := mul_le_mul_of_nonneg_left
    (scheduledWindow_real_upper κ C hκ Lmin U) (Nat.cast_nonneg A : (0 : ℝ) ≤ A)
  have heq : (A : ℝ) * ((Lmin : ℝ) +
      (4 * Real.log ((U : ℝ) + 2) + max C 0) / κ + 1) + B =
      (4 * (A : ℝ) / κ) * Real.log ((U : ℝ) + 2) +
      ((A : ℝ) * ((Lmin : ℝ) + max C 0 / κ + 1) + B) := by ring
  dsimp [scheduledSpan]
  push_cast
  linarith

/-- The fixed-tree span really is O(log U), with no hidden dependence on U. -/
theorem scheduledSpan_isBigO_log (κ C : ℝ) (hκ : 0 < κ) (A B Lmin : ℕ) :
    (fun U : ℕ => (scheduledSpan κ C A B Lmin U : ℝ)) =O[atTop]
      (fun U : ℕ => Real.log (U : ℝ)) := by
  let a : ℝ := 4 * (A : ℝ) / κ
  let c : ℝ := (A : ℝ) * ((Lmin : ℝ) + max C 0 / κ + 1) + B
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlog := (Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun U : ℕ => (U : ℝ)) atTop atTop)).eventually
      (eventually_ge_atTop (1 : ℝ))
  rw [isBigO_iff]
  refine ⟨2 * a + c, ?_⟩
  filter_upwards [hlog, eventually_ge_atTop (2 : ℕ)] with U hlogU hU
  change 1 ≤ Real.log (U : ℝ) at hlogU
  have hUr : (2 : ℝ) ≤ U := by exact_mod_cast hU
  have hsquare : (U : ℝ) + 2 ≤ (U : ℝ) ^ 2 := by
    have hp : 0 ≤ ((U : ℝ) - 2) * ((U : ℝ) + 1) := by positivity
    nlinarith
  have hshiftlog : Real.log ((U : ℝ) + 2) ≤ 2 * Real.log (U : ℝ) := by
    have hm := Real.log_le_log (by positivity : 0 < (U : ℝ) + 2) hsquare
    simpa only [Real.log_pow, Nat.cast_ofNat] using hm
  have hupper := scheduledSpan_real_upper κ C hκ A B Lmin U
  have hbound : (scheduledSpan κ C A B Lmin U : ℝ) ≤
      (2 * a + c) * Real.log (U : ℝ) := by
    change (scheduledSpan κ C A B Lmin U : ℝ) ≤
      a * Real.log ((U : ℝ) + 2) + c at hupper
    nlinarith [mul_le_mul_of_nonneg_left hshiftlog ha,
      mul_le_mul_of_nonneg_left hlogU hc]
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (scheduledSpan κ C A B Lmin U) :
      (0 : ℝ) ≤ scheduledSpan κ C A B Lmin U),
    abs_of_nonneg (by linarith : 0 ≤ Real.log (U : ℝ))] using hbound

/-- The actual affine template span satisfies T(U)/U → 0. -/
theorem scheduledSpan_div_tendsto_zero (κ C : ℝ) (hκ : 0 < κ)
    (A B Lmin : ℕ) :
    Tendsto (fun U : ℕ => (scheduledSpan κ C A B Lmin U : ℝ) / (U : ℝ))
      atTop (𝓝 0) := by
  let c : ℝ := (A : ℝ) * ((Lmin : ℝ) + max C 0 / κ + 1) + B
  have hc : Tendsto (fun x : ℝ => c / x) atTop (𝓝 0) :=
    (isLittleO_const_id_atTop c).tendsto_div_nhds_zero
  have ht : Tendsto (fun x : ℝ =>
      ((4 * (A : ℝ) / κ) * Real.log (x + 2) + c) / x) atTop (𝓝 0) := by
    convert (tendsto_shifted_log_div_id.const_mul (4 * (A : ℝ) / κ)).add hc using 1
    · ext x
      ring
    · norm_num
  have htn := ht.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun U : ℕ => (U : ℝ)) atTop atTop)
  refine squeeze_zero' (Eventually.of_forall fun U => by positivity)
    (Eventually.of_forall fun U => ?_) htn
  exact div_le_div_of_nonneg_right
    (scheduledSpan_real_upper κ C hκ A B Lmin U) (Nat.cast_nonneg U)

/-- Exact buffer cost for the ACTUAL finest-grid cell number. -/
theorem actual_buffer_cost_eq (q : ℕ) (k : ℤ) (α₀ s₁ : ℝ) (U T : ℕ) :
    4 * ((2 ^ (U + T + 2) : ℕ) : ℝ) * errorRadius q k α₀ s₁ U =
      ((q : ℝ) * (2 : ℝ) ^ (-k) + 1) *
        (2 : ℝ) ^ ((T : ℝ) + 4 - α₀ * ((U : ℝ) + (k : ℝ)) / s₁) := by
  have hscale : (4 : ℝ) * (2 : ℝ) ^ (U + T + 2) *
      (2 : ℝ) ^ (-(U : ℝ)) = (2 : ℝ) ^ ((T : ℝ) + 4) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
      ← Real.rpow_natCast, ← Real.rpow_add (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    push_cast
    ring
  unfold errorRadius
  push_cast
  calc
    _ = ((q : ℝ) * (2 : ℝ) ^ (-k) + 1) *
        ((4 : ℝ) * (2 : ℝ) ^ (U + T + 2) * (2 : ℝ) ^ (-(U : ℝ))) *
        (2 : ℝ) ^ (-α₀ * ((U : ℝ) + (k : ℝ)) / s₁) := by ring
    _ = _ := by
      rw [hscale, mul_assoc, ← Real.rpow_add (by norm_num)]
      congr 2
      ring

/-- Every sublinear span has vanishing positive-error double-buffer cost. -/
theorem sublinear_buffer_cost_tendsto_zero (q : ℕ) (k : ℤ) (α₀ s₁ : ℝ)
    (hα : 0 < α₀) (hs₁ : 0 < s₁) (T : ℕ → ℕ)
    (hT : Tendsto (fun U : ℕ => (T U : ℝ) / (U : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun U : ℕ => 4 * ((2 ^ (U + T U + 2) : ℕ) : ℝ) *
      errorRadius q k α₀ s₁ U) atTop (𝓝 0) := by
  let β : ℝ := α₀ / s₁
  have hβ : 0 < β := div_pos hα hs₁
  have ht : Tendsto (fun U : ℕ => (T U : ℝ) / (U : ℝ) - β)
      atTop (𝓝 (-β)) := by simpa using hT.sub_const β
  have hmul := ht.neg_mul_atTop (neg_lt_zero.mpr hβ)
    (tendsto_natCast_atTop_atTop : Tendsto (fun U : ℕ => (U : ℝ)) atTop atTop)
  have hshift := tendsto_atBot_add_const_right atTop (4 - β * (k : ℝ)) hmul
  have hexp : Tendsto (fun U : ℕ =>
      (T U : ℝ) + 4 - α₀ * ((U : ℝ) + (k : ℝ)) / s₁) atTop atBot := by
    apply hshift.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with U hU
    have hUr : (U : ℝ) ≠ 0 := by exact_mod_cast hU.ne'
    dsimp [β]
    field_simp
    ring
  have hpowers := (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp hexp
  have hcost := hpowers.const_mul ((q : ℝ) * (2 : ℝ) ^ (-k) + 1)
  simpa only [Function.comp_def, mul_zero, ← actual_buffer_cost_eq] using hcost

theorem scheduled_buffer_cost_tendsto_zero (q : ℕ) (k : ℤ) (α₀ s₁ κ C : ℝ)
    (hα : 0 < α₀) (hs₁ : 0 < s₁) (hκ : 0 < κ) (A B Lmin : ℕ) :
    Tendsto (fun U : ℕ =>
      4 * ((2 ^ (U + scheduledSpan κ C A B Lmin U + 2) : ℕ) : ℝ) *
        errorRadius q k α₀ s₁ U) atTop (𝓝 0) :=
  sublinear_buffer_cost_tendsto_zero q k α₀ s₁ hα hs₁ _
    (scheduledSpan_div_tendsto_zero κ C hκ A B Lmin)

/-- Both strict budgets hold together, with a positive radius, arbitrarily late. -/
theorem exists_late_robust_schedule (C₀ p κ α₀ s₁ : ℝ)
    (hC₀ : 0 < C₀) (hp : 0 < p) (hκ : 0 < κ)
    (hα : 0 < α₀) (hs₁ : 0 < s₁) (q : ℕ) (k : ℤ)
    (A B Lmin Umin : ℕ) :
    ∃ U L : ℕ, Umin ≤ U ∧ Lmin ≤ L ∧ A * L + B ≤ U ∧
      0 ≤ (U : ℝ) + (k : ℝ) ∧
      C₀ * ((U : ℝ) + 1) ^ 2 * Real.exp (-κ * (L : ℝ)) < p ∧
      0 < errorRadius q k α₀ s₁ U ∧
      4 * ((2 ^ (U + (A * L + B) + 2) : ℕ) : ℝ) *
        errorRadius q k α₀ s₁ U < p := by
  let C := Real.log (C₀ / p) + 1
  have hbuffer := (scheduled_buffer_cost_tendsto_zero q k α₀ s₁ κ C
    hα hs₁ hκ A B Lmin).eventually_lt_const hp
  have hspan := scheduledWindow_affine_span_eventually κ C hκ A B Lmin
  have hUk :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun U : ℕ => (U : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop (-(k : ℝ)))
  obtain ⟨U, hbuf, hsp, hlate, huk⟩ :=
    (hbuffer.and (hspan.and ((eventually_ge_atTop Umin).and hUk))).exists
  refine ⟨U, scheduledWindow κ C Lmin U, hlate,
    scheduledWindow_ge κ C Lmin U, hsp, by linarith, ?_,
    errorRadius_pos q k α₀ s₁ U, hbuf⟩
  exact entropy_budget_of_log_lower C₀ p κ _ hC₀ hp U
    (by simpa [C, add_assoc] using scheduledWindow_log_lower κ C hκ Lmin U)

end ContinuumRemainder
