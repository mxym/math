import ErdosSimilarityGrowingGaps.VariableBridge

namespace ErdosSimilarityGrowingGaps

open Filter Topology Asymptotics

/-! Squaring the gap-envelope base is still sublinear.  The proof keeps the
logarithmic exponent visible, rather than trying to multiply two unrelated
`o(U)` estimates. -/
theorem variable_eighth_power_squared_littleO
    {ι : Type*} {l : Filter ι} (p : ℝ) (hp : 0 < p) (hp₁ : p ≤ 1)
    (D U : ι → ℝ) (hU : Tendsto U l atTop)
    (hD₁ : ∀ᶠ i in l, 1 ≤ D i)
    (hD : D =o[l] (fun i => Real.log (Real.log (U i)))) :
    (fun i => ((((8 * variableBranching p (D i)) ^
      (variableDepth p (variableBranching p (D i)) + 1) : ℕ) : ℝ) ^ 2)) =o[l] U := by
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
      have hpk : 0 < p := hp
      have hratio : 1 < 2 / p := by
        apply (lt_div_iff₀ hp).2
        nlinarith [hp₁]
      have hlog : 0 < Real.log (2 / p) := Real.log_pos hratio
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
  have hlog8O : (fun i => Real.log (8 * (M i : ℝ))) =O[l]
      (fun i => Real.log (2 * (M i : ℝ))) := by
    apply IsBigO.of_bound 3
    filter_upwards [] with i
    have hMi : 2 ≤ M i := by
      dsimp [M]
      exact variableBranching_ge_two _ _
    have hMreal : (2 : ℝ) ≤ M i := by exact_mod_cast hMi
    have hbase : 0 < 2 * (M i : ℝ) := by positivity
    have hpow : 8 * (M i : ℝ) ≤ (2 * (M i : ℝ)) ^ (3 : ℕ) := by
      have hMnonneg : 0 ≤ (M i : ℝ) := by positivity
      have hMone : (1 : ℝ) ≤ (M i : ℝ) ^ 2 := by
        nlinarith [sq_nonneg ((M i : ℝ) - 1)]
      have hMpow : (M i : ℝ) ≤ (M i : ℝ) ^ 3 := by
        have h := mul_le_mul_of_nonneg_left hMone hMnonneg
        nlinarith
      nlinarith [hMpow]
    have hlog : Real.log (8 * (M i : ℝ)) ≤
        3 * Real.log (2 * (M i : ℝ)) := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < 8 * M i) hpow
      rw [Real.log_pow] at h
      norm_num at h ⊢
      exact h
    have hlog2nonneg : 0 ≤ Real.log (2 * (M i : ℝ)) :=
      Real.log_nonneg (by nlinarith)
    have hlog8nonneg : 0 ≤ Real.log (8 * (M i : ℝ)) :=
      Real.log_nonneg (by nlinarith [hMreal])
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hlog8nonneg, abs_of_nonneg hlog2nonneg]
    exact hlog
  have hlog8 : (fun i => Real.log (8 * (M i : ℝ))) =o[l]
      (fun i => Real.log (U i)) := hlog8O.trans_isLittleO hlog2
  have hlog8d : (fun i => (d i : ℝ) * Real.log (8 * (M i : ℝ))) =o[l]
      (fun i => Real.log (U i)) := by
    have hmul := (isBigO_refl (fun i => (d i : ℝ)) l).mul hlog8O
    exact hmul.trans_isLittleO hf
  have hnext : (fun i => 2 * ((d i : ℝ) + 1) *
      Real.log (8 * (M i : ℝ))) =o[l] (fun i => Real.log (U i)) := by
    have hadd := hlog8d.add hlog8
    have hscaled := hadd.const_mul_left 2
    convert hscaled using 1 <;> ext i <;> ring
  have he := exp_littleO_of_littleO_log
    (fun i => 2 * ((d i : ℝ) + 1) * Real.log (8 * (M i : ℝ)))
    U hU hnext 1
  have heq : (fun i =>
      ((((8 * M i) ^ (d i + 1) : ℕ) : ℝ) ^ 2)) =ᶠ[l]
      (fun i => Real.exp (2 * ((d i : ℝ) + 1) *
        Real.log (8 * (M i : ℝ)))) := by
    filter_upwards [] with i
    calc
      ((((8 * M i) ^ (d i + 1) : ℕ) : ℝ) ^ 2) =
          ((8 * (M i : ℝ)) ^ (d i + 1)) ^ 2 := by
            norm_num [Nat.cast_pow]
      _ = Real.exp (Real.log (((8 * (M i : ℝ)) ^ (d i + 1)) ^ 2)) := by
            symm
            have hMi : 2 ≤ M i := by
              dsimp [M]
              exact variableBranching_ge_two _ _
            have hbase : 0 < 8 * (M i : ℝ) := by
              have hMn : 0 < M i := by omega
              exact_mod_cast (Nat.mul_pos (by norm_num) hMn)
            have hpowpos : 0 < (8 * (M i : ℝ)) ^ (d i + 1) :=
              pow_pos hbase _
            exact Real.exp_log (by positivity)
      _ = Real.exp (2 * ((d i : ℝ) + 1) *
          Real.log (8 * (M i : ℝ))) := by
            rw [Real.log_pow, Real.log_pow]
            norm_num
            ring
  have he' : (fun i => Real.exp (2 * ((d i : ℝ) + 1) *
      Real.log (8 * (M i : ℝ)))) =o[l] U := by
    simpa [one_mul] using he
  exact he'.congr' heq.symm (Filter.Eventually.of_forall (fun _ => rfl))

end ErdosSimilarityGrowingGaps
