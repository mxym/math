import ErdosSimilarityGrowingGaps.VariableTree
import ErdosSimilarityGrowingGaps.RoutingEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! Parameters from paper (19) follow the annular width.  The first analytic
step records the changing depth and branching in the same asymptotic estimate. -/

noncomputable def variableBranching (p D : ℝ) : ℕ :=
  2 + Nat.ceil (24 * D / p)

noncomputable def variableDepth (p : ℝ) (b : ℕ) : ℕ :=
  Nat.ceil ((2 : ℝ) ^ ((b : ℝ) - 1) * Real.log (2 / p))

theorem variableBranching_ge_two (p D : ℝ) : 2 ≤ variableBranching p D := by
  unfold variableBranching
  omega

theorem variableBranching_upper (p D : ℝ) (hp : 0 < p) (hD : 0 ≤ D) :
    (variableBranching p D : ℝ) ≤ 3 + 24 * D / p := by
  have hx : 0 ≤ 24 * D / p := by positivity
  have hc := Nat.ceil_lt_add_one hx
  unfold variableBranching
  push_cast
  linarith

theorem variableBranching_bigO_width {ι : Type*} {l : Filter ι}
    (p : ℝ) (hp : 0 < p) (D : ι → ℝ) (hD : ∀ᶠ i in l, 1 ≤ D i) :
    (fun i => (variableBranching p (D i) : ℝ)) =O[l] D := by
  apply IsBigO.of_bound (3 + 24 / p)
  filter_upwards [hD] with i hi
  have hb := variableBranching_upper p (D i) hp (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ D i)]
  have heq : 24 * D i / p = (24 / p) * D i := by ring
  rw [heq] at hb
  nlinarith

/-- Exponentiating a quantity little-o of `log t` remains little-o of `t`.
This keeps the argument valid whether the quantity is bounded or unbounded. -/
theorem exp_littleO_of_littleO_log {ι : Type*} {l : Filter ι}
    (b t : ι → ℝ) (ht : Tendsto t l atTop)
    (hb : b =o[l] fun i => Real.log (t i)) (C : ℝ) :
    (fun i => Real.exp (C * b i)) =o[l] t := by
  have htlog : Tendsto (fun i => Real.log (t i)) l atTop :=
    Real.tendsto_log_atTop.comp ht
  have hsmall := (hb.const_mul_left C).def (by norm_num : (0 : ℝ) < 1 / 2)
  have hpos := htlog.eventually_ge_atTop 0
  have hdiff : Tendsto (fun i => Real.log (t i) - C * b i) l atTop := by
    apply tendsto_atTop_mono' l _ (htlog.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [hsmall, hpos] with i hi hlog
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog] at hi
    have hc : C * b i ≤ |C * b i| := le_abs_self _
    linarith
  have he : (fun i => Real.exp (C * b i)) =o[l] fun i => Real.exp (Real.log (t i)) :=
    Real.isLittleO_exp_comp_exp_comp.2 hdiff
  apply he.trans_eventuallyEq
  filter_upwards [ht.eventually_gt_atTop 0] with i hi
  exact Real.exp_log hi

/-- A uniform elementary envelope for the changing default depth. -/
theorem variableDepth_log_bound (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (b : ℕ) (hb : 2 ≤ b) :
    (variableDepth p b : ℝ) * Real.log (2 * (b : ℝ)) ≤
      2 * (1 + Real.log (2 / p)) * Real.exp (2 * (b : ℝ)) := by
  have hbr : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbn : (0 : ℝ) ≤ b := by positivity
  have hquot : 1 ≤ 2 / p := (le_div_iff₀ hp).2 (by linarith)
  have hC : 0 ≤ Real.log (2 / p) := Real.log_nonneg hquot
  have hlog₂ : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hr : (2 : ℝ) ^ ((b : ℝ) - 1) ≤ Real.exp (b : ℝ) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    apply Real.exp_le_exp.2
    nlinarith
  have hx : 0 ≤ (2 : ℝ) ^ ((b : ℝ) - 1) * Real.log (2 / p) :=
    mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le hC
  have hc := Nat.ceil_lt_add_one hx
  have hd : (variableDepth p b : ℝ) ≤
      1 + Real.exp (b : ℝ) * Real.log (2 / p) := by
    unfold variableDepth
    have hmul := mul_le_mul_of_nonneg_right hr hC
    linarith
  have hE : 1 ≤ Real.exp (b : ℝ) := Real.one_le_exp_iff.2 hbn
  have hd' : (variableDepth p b : ℝ) ≤
      (1 + Real.log (2 / p)) * Real.exp (b : ℝ) := by nlinarith
  have hl0 : 0 ≤ Real.log (2 * (b : ℝ)) := Real.log_nonneg (by linarith)
  have hl : Real.log (2 * (b : ℝ)) ≤ 2 * (b : ℝ) :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hbE : (b : ℝ) ≤ Real.exp (b : ℝ) := by
    linarith [Real.add_one_le_exp (b : ℝ)]
  calc
    _ ≤ ((1 + Real.log (2 / p)) * Real.exp (b : ℝ)) * (2 * Real.exp (b : ℝ)) := by
      apply mul_le_mul hd' (hl.trans (by linarith)) hl0
      positivity
    _ = _ := by
      rw [show (2 : ℝ) * (b : ℝ) = (b : ℝ) + b by ring, Real.exp_add]
      ring

/-- Paper (24): the depth and branching can both vary with the same annulus.
No fixed-tree coefficient is used in this estimate. -/
theorem variableDepth_log_littleO
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] fun i => Real.log (Real.log (U i))) :
    (fun i => (variableDepth p (variableBranching p (D i)) : ℝ) *
      Real.log (2 * (variableBranching p (D i) : ℝ))) =o[l]
      (fun i => Real.log (U i)) := by
  have hb := (variableBranching_bigO_width p hp D hD₁).trans_isLittleO hD
  have he := exp_littleO_of_littleO_log
    (fun i => (variableBranching p (D i) : ℝ))
    (fun i => Real.log (U i)) (Real.tendsto_log_atTop.comp hU) hb 2
  have hbound : (fun i => (variableDepth p (variableBranching p (D i)) : ℝ) *
      Real.log (2 * (variableBranching p (D i) : ℝ))) =O[l]
      (fun i => Real.exp (2 * (variableBranching p (D i) : ℝ))) := by
    apply IsBigO.of_bound (2 * (1 + Real.log (2 / p)))
    apply Eventually.of_forall
    intro i
    have hb₂ := variableBranching_ge_two p (D i)
    have hbr : (2 : ℝ) ≤ variableBranching p (D i) := by exact_mod_cast hb₂
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg (by linarith))), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact variableDepth_log_bound p hp hp₁ _ hb₂
  exact hbound.trans_isLittleO he

end ErdosSimilarityGrowingGaps

namespace ErdosSimilarityGrowingGaps

/-- The paper's default-depth choice discharges the no-default budget directly. -/
theorem variableDepth_default_budget (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (b : ℕ) (hb : 2 ≤ b) :
    (1 - (2 : ℝ) ^ (1 - (b : ℝ))) ^ variableDepth p b ≤ p / 2 := by
  have hbase : 0 < (2 : ℝ) ^ (1 - (b : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hbase_lt : (2 : ℝ) ^ (1 - (b : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
      have hb' : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
      linarith)
  have hq : 0 ≤ 1 - (2 : ℝ) ^ (1 - (b : ℝ)) := by linarith
  have hpow := pow_le_pow_left₀ hq
    (Real.one_sub_le_exp_neg ((2 : ℝ) ^ (1 - (b : ℝ)))) (variableDepth p b)
  have hceil :
      (2 : ℝ) ^ ((b : ℝ) - 1) * Real.log (2 / p) ≤ variableDepth p b := by
    unfold variableDepth
    exact_mod_cast Nat.le_ceil _
  have htwo :
      (2 : ℝ) ^ (1 - (b : ℝ)) *
          ((2 : ℝ) ^ ((b : ℝ) - 1) * Real.log (2 / p)) = Real.log (2 / p) := by
    calc
      _ = ((2 : ℝ) ^ (1 - (b : ℝ)) * (2 : ℝ) ^ ((b : ℝ) - 1)) * Real.log (2 / p) := by ring
      _ = (2 : ℝ) ^ ((1 - (b : ℝ)) + ((b : ℝ) - 1)) * Real.log (2 / p) := by
        rw [← Real.rpow_add (by norm_num)]
      _ = Real.log (2 / p) := by norm_num
  have hlog : Real.log (2 / p) ≥ Real.log 2 := by
    apply Real.log_le_log (by norm_num)
    exact (le_div_iff₀ hp).2 (by linarith)
  have hexp : Real.exp (-Real.log (2 / p)) = p / 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hpow' : (1 - (2 : ℝ) ^ (1 - (b : ℝ))) ^ variableDepth p b ≤
      Real.exp (-((2 : ℝ) ^ (1 - (b : ℝ)) * (variableDepth p b : ℝ))) := by
    calc
      _ ≤ Real.exp (-((2 : ℝ) ^ (1 - (b : ℝ)))) ^ variableDepth p b := hpow
      _ = Real.exp (((variableDepth p b : ℝ) *
          (-(2 : ℝ) ^ (1 - (b : ℝ))))) := by
        rw [Real.exp_nat_mul]
      _ = Real.exp (-((2 : ℝ) ^ (1 - (b : ℝ)) * (variableDepth p b : ℝ))) := by
        congr 1 <;> ring
  calc
    _ ≤ Real.exp (-((2 : ℝ) ^ (1 - (b : ℝ)) * variableDepth p b)) := hpow'
    _ ≤ Real.exp (-Real.log (2 / p)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hceil hbase.le, htwo]
    _ = p / 2 := hexp

end ErdosSimilarityGrowingGaps
