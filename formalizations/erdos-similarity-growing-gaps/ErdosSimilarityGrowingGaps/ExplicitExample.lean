import ErdosSimilarityGrowingGaps.Input
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace ErdosSimilarityGrowingGaps

open Filter Set Topology

/-- The exact reindexing `n + 1` discards the zero logarithmic scale at index zero. -/
noncomputable def explicitLogScaleValue (β : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (Real.log (Real.log ((n : ℝ) + 21))) ^ β

noncomputable def exampleLogLog (n : ℕ) : ℝ := Real.log (Real.log ((n : ℝ) + 21))

theorem example_inner_log_gt_one (n : ℕ) : 1 < Real.log ((n : ℝ) + 21) := by
  apply (Real.lt_log_iff_exp_lt (by positivity)).2
  have := Real.exp_one_lt_three
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem explicitLogScaleValue_loglog_pos (n : ℕ) : 0 < exampleLogLog n :=
  Real.log_pos (example_inner_log_gt_one n)

theorem exampleLogLog_monotone : Monotone exampleLogLog := by
  intro n m hnm
  apply Real.log_le_log (by linarith [example_inner_log_gt_one n])
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 21

theorem exampleLogLog_tendsto : Tendsto exampleLogLog atTop atTop := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 21) atTop atTop :=
    tendsto_atTop_add_const_right atTop 21 tendsto_natCast_atTop_atTop
  exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hcast)

theorem examplePower_tendsto {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n => exampleLogLog n ^ β) atTop atTop :=
  (tendsto_rpow_atTop hβ).comp exampleLogLog_tendsto

theorem explicitLogScaleValue_strictMono {β : ℝ} (hβ : 0 < β) :
    StrictMono (explicitLogScaleValue β) := by
  intro n m hnm
  have hnmR : (n : ℝ) + 1 < (m : ℝ) + 1 := by exact_mod_cast Nat.add_lt_add_right hnm 1
  have hpow : exampleLogLog n ^ β ≤ exampleLogLog m ^ β :=
    Real.rpow_le_rpow (explicitLogScaleValue_loglog_pos n).le
      (exampleLogLog_monotone hnm.le) hβ.le
  have hmul := mul_lt_mul_of_pos_right hnmR
    (Real.rpow_pos_of_pos (explicitLogScaleValue_loglog_pos n) β)
  exact hmul.trans_le (mul_le_mul_of_nonneg_left hpow (by positivity))

theorem explicitLogScaleValue_tendsto_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (explicitLogScaleValue β) atTop atTop := by
  apply tendsto_atTop_mono' atTop _ tendsto_natCast_atTop_atTop
  filter_upwards [(examplePower_tendsto hβ).eventually (eventually_ge_atTop (1 : ℝ))] with n hn
  change (n : ℝ) ≤ ((n : ℝ) + 1) * exampleLogLog n ^ β
  change 1 ≤ exampleLogLog n ^ β at hn
  have := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (n : ℝ) + 1)
  nlinarith

theorem explicitLogScaleValue_gap_tendsto_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n : ℕ => explicitLogScaleValue β (n + 1) -
      explicitLogScaleValue β n) atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_) (examplePower_tendsto hβ)
  have hmono : exampleLogLog n ^ β ≤ exampleLogLog (n + 1) ^ β :=
    Real.rpow_le_rpow (explicitLogScaleValue_loglog_pos n).le
      (exampleLogLog_monotone (Nat.le_succ n)) hβ.le
  have hmul := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ (n : ℝ) + 1)
  change exampleLogLog n ^ β ≤
    ((↑(n + 1) : ℝ) + 1) * exampleLogLog (n + 1) ^ β -
      ((n : ℝ) + 1) * exampleLogLog n ^ β
  push_cast
  nlinarith

noncomputable def explicitLogScale (β : ℝ) (hβ : 0 < β) : LogScale where
  z := explicitLogScaleValue β
  strictMono := explicitLogScaleValue_strictMono hβ
  tendsto_atTop := explicitLogScaleValue_tendsto_atTop hβ
  positive := fun n => mul_pos (by positivity)
    (Real.rpow_pos_of_pos (explicitLogScaleValue_loglog_pos n) β)

theorem explicitLogScale_input_ratio_tendsto_zero {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n : ℕ => input (explicitLogScale β hβ) (n + 1) /
      input (explicitLogScale β hβ) n) atTop (𝓝 0) := by
  apply input_ratio_tendsto_zero
  exact explicitLogScaleValue_gap_tendsto_atTop hβ

/-- Quantitative logarithmic increment, used twice below. -/
theorem log_increment_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log b - Real.log a ≤ (b - a) / a := by
  rw [← Real.log_div hb.ne' ha.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  have heq : b / a - 1 = (b - a) / a := by field_simp
  exact h.trans_eq heq

theorem exampleLogLog_increment_bound (n : ℕ) :
    exampleLogLog (n + 1) - exampleLogLog n ≤ 1 / ((n : ℝ) + 21) := by
  have hx : 0 < (n : ℝ) + 21 := by positivity
  have hlog : 1 ≤ Real.log ((n : ℝ) + 21) := (example_inner_log_gt_one n).le
  have h₁ := log_increment_bound hx (show 0 < (n : ℝ) + 22 by positivity)
  have h₂ := log_increment_bound (a := Real.log ((n : ℝ) + 21))
    (b := Real.log ((n : ℝ) + 22)) (by linarith [hlog])
    (show 0 < Real.log ((n : ℝ) + 22) by
      apply Real.log_pos; have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hincr : Real.log ((n : ℝ) + 22) - Real.log ((n : ℝ) + 21) ≤
      1 / ((n : ℝ) + 21) := by convert h₁ using 1 <;> ring
  have hdiv : (Real.log ((n : ℝ) + 22) - Real.log ((n : ℝ) + 21)) /
      Real.log ((n : ℝ) + 21) ≤ 1 / ((n : ℝ) + 21) := by
    apply (div_le_iff₀ (by linarith [hlog])).2
    exact hincr.trans (le_mul_of_one_le_right (by positivity) hlog)
  convert h₂.trans hdiv using 1 <;> norm_num [exampleLogLog, Nat.cast_add, Nat.cast_one, add_assoc]

/-- A fractional power increment is bounded using its multiplicative ratio.
This avoids an appeal to a differentiability statement at zero. -/
theorem fractional_power_increment {A B β : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hβ : 0 < β) (hβ₁ : β ≤ 1) :
    B ^ β - A ^ β ≤ A ^ β * (B - A) / A := by
  have hB : 0 < B := hA.trans_le hAB
  have hratio : 1 ≤ B / A := (le_div_iff₀ hA).2 (by simpa using hAB)
  have hpow : (B / A) ^ β ≤ B / A := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hratio hβ₁
  have hmul := mul_le_mul_of_nonneg_left hpow (Real.rpow_pos_of_pos hA β).le
  rw [Real.div_rpow hB.le hA.le] at hmul
  have hAz : A ^ β ≠ 0 := (Real.rpow_pos_of_pos hA β).ne'
  field_simp at hmul ⊢
  nlinarith

theorem explicitLogScaleValue_gap_bound {β : ℝ} (hβ : 0 < β) (hβ₁ : β ≤ 1)
    {n : ℕ} (hL : 1 ≤ exampleLogLog n) :
    explicitLogScaleValue β (n + 1) - explicitLogScaleValue β n ≤
      2 * exampleLogLog n ^ β := by
  let A := exampleLogLog n
  let B := exampleLogLog (n + 1)
  let P := A ^ β
  have hA : 0 < A := explicitLogScaleValue_loglog_pos n
  have hP : 0 < P := Real.rpow_pos_of_pos hA β
  have hx : 0 < (n : ℝ) + 21 := by positivity
  have hdiff := fractional_power_increment hA (exampleLogLog_monotone (Nat.le_succ n)) hβ hβ₁
  have hinc := exampleLogLog_increment_bound n
  have hdiff' : B ^ β - P ≤ P / ((n : ℝ) + 21) := by
    calc
      B ^ β - P ≤ P * (B - A) / A := hdiff
      _ ≤ P * (1 / ((n : ℝ) + 21)) / A := by
        apply div_le_div_of_nonneg_right _ hA.le
        exact mul_le_mul_of_nonneg_left hinc hP.le
      _ ≤ P / ((n : ℝ) + 21) := by
        apply (div_le_iff₀ hA).2
        simpa only [mul_one_div] using le_mul_of_one_le_right
          (div_nonneg hP.le hx.le) hL
  have hweighted := mul_le_mul_of_nonneg_left hdiff'
    (by positivity : 0 ≤ (n : ℝ) + 2)
  have hquot : ((n : ℝ) + 2) * (P / ((n : ℝ) + 21)) ≤ P := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hx).2
    nlinarith
  change ((↑(n + 1) : ℝ) + 1) * B ^ β - ((n : ℝ) + 1) * P ≤ 2 * P
  push_cast
  nlinarith


theorem explicitLogScale_consecutiveGapLittleO {β : ℝ} (hβ : 0 < β) (hβ₁ : β < 1) :
    ConsecutiveLogGapLittleO (explicitLogScale β hβ) := by
  intro ε hε
  have hneg : Tendsto (fun n : ℕ => exampleLogLog n ^ (β - 1)) atTop (𝓝 0) := by
    have hpos : 0 < 1 - β := sub_pos.mpr hβ₁
    convert (tendsto_rpow_neg_atTop hpos).comp exampleLogLog_tendsto using 1
    ext n
    congr 1
    ring
  have hev : ∀ᶠ n : ℕ in atTop,
      exampleLogLog n ^ (β - 1) ≤ ε / 2 :=
    hneg.eventually (eventually_le_nhds (by positivity))
  have hP : Tendsto (fun n : ℕ => exampleLogLog n ^ β) atTop atTop :=
    examplePower_tendsto hβ
  have hevP : ∀ᶠ n : ℕ in atTop, 2 ≤ exampleLogLog n ^ β :=
    hP.eventually (eventually_ge_atTop 2)
  have hN : ∀ᶠ n : ℕ in atTop, 19 ≤ n := eventually_ge_atTop 19
  have hevfinal : ∀ᶠ n : ℕ in atTop,
      1 < Real.log (explicitLogScaleValue β n) ∧
        explicitLogScaleValue β (n + 1) - explicitLogScaleValue β n ≤
          ε * Real.log (Real.log (explicitLogScaleValue β n)) := by
    filter_upwards [hev, hevP, hN] with n hnNeg hnP hnN
    have hA : 0 < exampleLogLog n := explicitLogScaleValue_loglog_pos n
    have hnNr : (19 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
    have hinnerpos : 0 < Real.log ((n : ℝ) + 21) := by
      apply Real.log_pos
      have hnreal : (1 : ℝ) < (n : ℝ) + 21 := by linarith [show (0 : ℝ) ≤ n by positivity]
      exact hnreal
    have hA1 : 1 ≤ exampleLogLog n := by
      change 1 ≤ Real.log (Real.log ((n : ℝ) + 21))
      apply (Real.le_log_iff_exp_le hinnerpos).2
      apply (Real.le_log_iff_exp_le (by positivity)).2
      have he := Real.exp_one_lt_three
      have hexp3 : Real.exp 3 < 27 := by
        rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
        convert pow_lt_pow_left₀ he (by positivity) (n := 3) (by norm_num) using 1 <;> norm_num
      have heexp : Real.exp (Real.exp 1) < Real.exp 3 :=
        Real.exp_lt_exp.mpr he
      have hnreal : (27 : ℝ) < (n : ℝ) + 21 := by linarith
      exact heexp.le.trans (hexp3.le.trans hnreal.le)
    have hpowrel : explicitLogScaleValue β n =
        ((n : ℝ) + 1) * exampleLogLog n ^ β := rfl
    have hzlarge : (n : ℝ) + 21 ≤ explicitLogScaleValue β n := by
      rw [hpowrel]
      have hncoef : 0 ≤ (n : ℝ) + 1 := by positivity
      have hmul : 2 * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) * exampleLogLog n ^ β := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left hnP hncoef
      nlinarith
    have hlogzpos : 0 < Real.log (explicitLogScaleValue β n) := by
      apply Real.log_pos
      have hexp : Real.exp 1 < (n : ℝ) + 21 := by
        have he := Real.exp_one_lt_three
        have hnreal : (3 : ℝ) < (n : ℝ) + 21 := by linarith
        exact he.trans hnreal
      have hone : (1 : ℝ) < Real.exp 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_lt_exp.2 (by norm_num)
      exact hone.trans (hexp.trans_le hzlarge)
    have hden : exampleLogLog n ≤
        Real.log (Real.log (explicitLogScaleValue β n)) := by
      apply Real.log_le_log hinnerpos
      exact Real.log_le_log (by positivity) hzlarge
    have hgap := explicitLogScaleValue_gap_bound hβ hβ₁.le hA1
    have hpowbound : exampleLogLog n ^ β ≤ (ε / 2) * exampleLogLog n := by
      rw [show β = (β - 1) + 1 by ring, Real.rpow_add hA]
      rw [Real.rpow_one]
      exact mul_le_mul_of_nonneg_right hnNeg hA.le
    have hfinal : explicitLogScaleValue β (n + 1) - explicitLogScaleValue β n ≤
        ε * Real.log (Real.log (explicitLogScaleValue β n)) := by
      calc
        explicitLogScaleValue β (n + 1) - explicitLogScaleValue β n ≤
            2 * exampleLogLog n ^ β := hgap
        _ ≤ ε * exampleLogLog n := by nlinarith
        _ ≤ ε * Real.log (Real.log (explicitLogScaleValue β n)) :=
          mul_le_mul_of_nonneg_left hden hε.le
    have hlogzgt : 1 < Real.log (explicitLogScaleValue β n) := by
      exact (example_inner_log_gt_one n).trans_le
        (Real.log_le_log (by positivity) hzlarge)
    exact ⟨hlogzgt, hfinal⟩
  rcases (eventually_atTop.1 hevfinal) with ⟨N, hNall⟩
  exact ⟨N, fun n hn => hNall n hn⟩


noncomputable def explicitOriginalInput (β : ℝ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(n : ℝ) * (Real.log (Real.log ((n : ℝ) + 20))) ^ β)

theorem explicitOriginalInput_shift {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    explicitOriginalInput β (n + 1) = input (explicitLogScale β hβ) n := by
  simp only [explicitOriginalInput, input, explicitLogScale, explicitLogScaleValue,
    Nat.cast_add, Nat.cast_one]
  congr 1
  have heq : (n : ℝ) + 1 + 20 = (n : ℝ) + 21 := by ring
  rw [heq]
  ring

theorem explicitOriginalInput_ratio_tendsto_zero {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n : ℕ => explicitOriginalInput β (n + 1) /
      explicitOriginalInput β n) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  simpa only [explicitOriginalInput_shift hβ] using
    explicitLogScale_input_ratio_tendsto_zero hβ


end ErdosSimilarityGrowingGaps
