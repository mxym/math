import ErdosSimilarityGrowingGaps.VariableRateSchedule
import ErdosSimilarityGrowingGaps.AnnulusSequence

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! Elementary asymptotic interfaces used when the late annulus is selected
from `WindowFilling`.  These lemmas keep the logarithmic width estimate in a
form that can be fed directly to the variable branching/depth schedule. -/

theorem tendsto_log_log_atTop_of_tendsto
    {ι : Type*} {l : Filter ι} (U : ι → ℝ)
    (hU : Tendsto U l atTop) :
    Tendsto (fun i => Real.log (Real.log (U i))) l atTop := by
  simpa [Function.comp_def] using
    (Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hU))

theorem eventually_additive_width_le_loglog
    {ι : Type*} {l : Filter ι} (D U : ι → ℝ)
    (hU : Tendsto U l atTop)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i))))
    (hD₀ : ∀ᶠ i in l, 0 ≤ D i)
    (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 < ε) :
    ∀ᶠ i in l, D i + δ ≤ ε * Real.log (Real.log (U i)) := by
  have hLL : Tendsto (fun i => Real.log (Real.log (U i))) l atTop :=
    tendsto_log_log_atTop_of_tendsto U hU
  have hLLpos : ∀ᶠ i in l, 0 < Real.log (Real.log (U i)) :=
    hLL.eventually_gt_atTop 0
  have hDsmall := hD.def (by positivity : 0 < ε / 2)
  have hδsmall : ∀ᶠ i in l,
      δ ≤ (ε / 2) * Real.log (Real.log (U i)) := by
    filter_upwards [hLL.eventually_ge_atTop (2 * δ / ε)] with i hi
    have hmul := (div_le_iff₀ hε).1 hi
    nlinarith
  filter_upwards [hDsmall, hD₀, hLLpos, hδsmall] with i hi hDi hLLi hδi
  rw [Real.norm_eq_abs, abs_of_nonneg hDi,
    Real.norm_eq_abs, abs_of_pos hLLi] at hi
  nlinarith

theorem variableBranching_littleO_loglog
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p)
    (D U : ι → ℝ) (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hU : Tendsto U l atTop)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => (variableBranching p (D i) : ℝ)) =o[l]
      (fun i => Real.log (Real.log (U i))) := by
  exact (variableBranching_bigO_width p hp D hD₁).trans_isLittleO hD

theorem variableDepth_log_littleO_of_window_width
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => (variableDepth p (variableBranching p (D i)) : ℝ) *
      Real.log (2 * (variableBranching p (D i) : ℝ))) =o[l]
      (fun i => Real.log (U i)) := by
  exact variableDepth_log_littleO p hp hp₁ D U hU hD₁ hD

/-! The coefficient multiplying the base length in the affine span is already
sublinear in the late origin.  This is the exponential form of
`variableDepth_log_littleO`; it is useful before choosing the integer base
length and the explicit stable gap. -/
theorem variable_length_coefficient_littleO
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => (((4 * variableBranching p (D i)) ^
      variableDepth p (variableBranching p (D i)) : ℕ) : ℝ)) =o[l] U := by
  let M : ι → ℕ := fun i => variableBranching p (D i)
  let d : ι → ℕ := fun i => variableDepth p (M i)
  have hf := variableDepth_log_littleO_of_window_width p hp hp₁ D U hU hD₁ hD
  have hcoef : (fun i => (d i : ℝ) * Real.log (4 * (M i : ℝ))) =O[l]
      (fun i => (d i : ℝ) * Real.log (2 * (M i : ℝ))) := by
    apply IsBigO.of_bound 2
    filter_upwards [] with i
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hMi : 2 ≤ M i := by
      dsimp [M]
      exact variableBranching_ge_two _ _
    have hMreal : (2 : ℝ) ≤ M i := by exact_mod_cast hMi
    have hlog4 : Real.log (4 * (M i : ℝ)) ≤
        2 * Real.log (2 * (M i : ℝ)) := by
      have h2M : (0 : ℝ) < 2 * M i := by positivity
      rw [show (4 : ℝ) * M i = 2 * (2 * M i) by ring,
        Real.log_mul (by norm_num) (ne_of_gt h2M)]
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (by nlinarith : (2 : ℝ) ≤ 2 * M i)
      nlinarith
    have hlog2 : 0 ≤ Real.log (2 * (M i : ℝ)) :=
      Real.log_nonneg (by nlinarith)
    have hlog4nonneg : 0 ≤ Real.log (4 * (M i : ℝ)) :=
      Real.log_nonneg (by nlinarith [hMreal])
    have hd : 0 ≤ (d i : ℝ) := by positivity
    have hleft : 0 ≤ (d i : ℝ) * Real.log (4 * (M i : ℝ)) :=
      mul_nonneg hd hlog4nonneg
    have hright : 0 ≤ (d i : ℝ) * Real.log (2 * (M i : ℝ)) :=
      mul_nonneg hd hlog2
    rw [abs_of_nonneg hleft, abs_of_nonneg hright]
    have hm := mul_le_mul_of_nonneg_left hlog4 hd
    nlinarith
  have hf4 : (fun i => (d i : ℝ) * Real.log (4 * (M i : ℝ))) =o[l]
      (fun i => Real.log (U i)) := hcoef.trans_isLittleO hf
  have he := exp_littleO_of_littleO_log
    (fun i => (d i : ℝ) * Real.log (4 * (M i : ℝ)))
    U hU hf4 1
  have heq : (fun i => ((((4 * M i) ^ d i : ℕ) : ℝ))) =ᶠ[l]
      (fun i => Real.exp ((d i : ℝ) * Real.log (4 * (M i : ℝ)))) := by
    filter_upwards [] with i
    calc
      (((4 * M i) ^ d i : ℕ) : ℝ) =
          (4 * (M i : ℝ)) ^ d i := by
            norm_num [Nat.cast_pow]
      _ = Real.exp (Real.log ((4 * (M i : ℝ)) ^ d i)) := by
            symm
            have hMi : 2 ≤ M i := by
              dsimp [M]
              exact variableBranching_ge_two _ _
            have hbase : 0 < 4 * (M i : ℝ) := by
              exact_mod_cast (show 0 < 4 * M i by omega)
            exact Real.exp_log (pow_pos hbase _)
      _ = Real.exp ((d i : ℝ) * Real.log (4 * (M i : ℝ))) := by
            rw [Real.log_pow]
  have he' : (fun i => Real.exp ((d i : ℝ) * Real.log (4 * (M i : ℝ)))) =o[l] U := by
    simpa [one_mul] using he
  exact he'.congr' heq.symm
    (Filter.Eventually.of_forall (fun _ => rfl))

theorem variable_edge_coefficient_littleO
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => (((4 * variableBranching p (D i)) ^
      (variableDepth p (variableBranching p (D i)) + 1) : ℕ) : ℝ)) =o[l] U := by
  let M : ι → ℕ := fun i => variableBranching p (D i)
  let d : ι → ℕ := fun i => variableDepth p (M i)
  have hf := variableDepth_log_littleO_of_window_width p hp hp₁ D U hU hD₁ hD
  have hlog2O : (fun i => Real.log (2 * (M i : ℝ))) =O[l]
      (fun i => (d i : ℝ) * Real.log (2 * (M i : ℝ))) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with i
    have hMi : 2 ≤ M i := by
      dsimp [M]
      exact variableBranching_ge_two _ _
    have hMreal : (2 : ℝ) ≤ M i := by exact_mod_cast hMi
    have hdpos : 0 < d i := by
      dsimp [d, variableDepth]
      apply Nat.ceil_pos.mpr
      have : 1 < 2 / p := by
        apply (lt_div_iff₀ hp).2
        nlinarith
      have : 0 < Real.log (2 / p) := Real.log_pos this
      positivity
    have hlog : 0 ≤ Real.log (2 * (M i : ℝ)) :=
      Real.log_nonneg (by nlinarith)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog]
    have hlogd : 0 ≤ (d i : ℝ) * Real.log (2 * (M i : ℝ)) := by positivity
    rw [abs_of_nonneg hlogd]
    have hd1 : (1 : ℝ) ≤ (d i : ℝ) := by
      exact_mod_cast (show 1 ≤ d i by omega)
    nlinarith
  have hlog2 := hlog2O.trans_isLittleO hf
  have hlog4O : (fun i => Real.log (4 * (M i : ℝ))) =O[l]
      (fun i => Real.log (2 * (M i : ℝ))) := by
    apply IsBigO.of_bound 2
    filter_upwards [] with i
    have hMi : 2 ≤ M i := by
      dsimp [M]
      exact variableBranching_ge_two _ _
    have hMreal : (2 : ℝ) ≤ M i := by exact_mod_cast hMi
    have hlog4 : Real.log (4 * (M i : ℝ)) ≤
        2 * Real.log (2 * (M i : ℝ)) := by
      have h2M : (0 : ℝ) < 2 * M i := by positivity
      rw [show (4 : ℝ) * M i = 2 * (2 * M i) by ring,
        Real.log_mul (by norm_num) (ne_of_gt h2M)]
      have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (by nlinarith [hMreal] : (2 : ℝ) ≤ 2 * M i)
      nlinarith
    have hlog2nonneg : 0 ≤ Real.log (2 * (M i : ℝ)) :=
      Real.log_nonneg (by nlinarith)
    have hlog4nonneg : 0 ≤ Real.log (4 * (M i : ℝ)) :=
      Real.log_nonneg (by nlinarith [hMreal])
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hlog4nonneg,
      abs_of_nonneg hlog2nonneg]
    exact hlog4
  have hlog4 := hlog4O.trans_isLittleO hlog2
  have hf4 : (fun i => (d i : ℝ) * Real.log (4 * (M i : ℝ))) =o[l]
      (fun i => Real.log (U i)) := by
    have hcoef : (fun i => (d i : ℝ) * Real.log (4 * (M i : ℝ))) =O[l]
        (fun i => (d i : ℝ) * Real.log (2 * (M i : ℝ))) := by
      apply IsBigO.of_bound 2
      filter_upwards [] with i
      have hMi : 2 ≤ M i := by
        dsimp [M]
        exact variableBranching_ge_two _ _
      have hlog2nonneg : 0 ≤ Real.log (2 * (M i : ℝ)) :=
        Real.log_nonneg (by
          have hMreal : (2 : ℝ) ≤ M i := by exact_mod_cast hMi
          nlinarith)
      have hlog4nonneg : 0 ≤ Real.log (4 * (M i : ℝ)) := by
        have hMreal : (2 : ℝ) ≤ M i := by exact_mod_cast hMi
        exact Real.log_nonneg (by nlinarith)
      have hlog4 : Real.log (4 * (M i : ℝ)) ≤
          2 * Real.log (2 * (M i : ℝ)) := by
        have h2M : (0 : ℝ) < 2 * M i := by positivity
        rw [show (4 : ℝ) * M i = 2 * (2 * M i) by ring,
          Real.log_mul (by norm_num) (ne_of_gt h2M)]
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
          (by
            have hMreal : (2 : ℝ) ≤ M i := by exact_mod_cast hMi
            nlinarith [hMreal] : (2 : ℝ) ≤ 2 * (M i : ℝ))
        nlinarith
      have hd : 0 ≤ (d i : ℝ) := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hd hlog4nonneg),
        abs_of_nonneg (mul_nonneg hd hlog2nonneg)]
      nlinarith [mul_le_mul_of_nonneg_left hlog4 hd]
    exact hcoef.trans_isLittleO hf
  have hnext : (fun i => ((d i : ℝ) + 1) *
      Real.log (4 * (M i : ℝ))) =o[l] (fun i => Real.log (U i)) := by
    have hadd := hf4.add hlog4
    convert hadd using 1 <;> ext i <;> ring
  have he := exp_littleO_of_littleO_log
    (fun i => ((d i : ℝ) + 1) * Real.log (4 * (M i : ℝ)))
    U hU hnext 1
  have heq : (fun i => ((((4 * M i) ^ (d i + 1) : ℕ) : ℝ))) =ᶠ[l]
      (fun i => Real.exp (((d i : ℝ) + 1) * Real.log (4 * (M i : ℝ)))) := by
    filter_upwards [] with i
    calc
      (((4 * M i) ^ (d i + 1) : ℕ) : ℝ) =
          (4 * (M i : ℝ)) ^ (d i + 1) := by norm_num [Nat.cast_pow]
      _ = Real.exp (Real.log ((4 * (M i : ℝ)) ^ (d i + 1))) := by
        symm
        have hbase : 0 < 4 * (M i : ℝ) := by
          have hMi : 2 ≤ M i := by
            dsimp [M]
            exact variableBranching_ge_two _ _
          have hMn : 0 < M i := by omega
          exact_mod_cast (Nat.mul_pos (by norm_num) hMn)
        exact Real.exp_log (pow_pos hbase _)
      _ = Real.exp (((d i : ℝ) + 1) * Real.log (4 * (M i : ℝ))) := by
        rw [Real.log_pow]
        congr 1
        norm_num
  have he' : (fun i => Real.exp (((d i : ℝ) + 1) *
      Real.log (4 * (M i : ℝ)))) =o[l] U := by
    simpa [one_mul] using he
  exact he'.congr' heq.symm (Filter.Eventually.of_forall (fun _ => rfl))

end ErdosSimilarityGrowingGaps
