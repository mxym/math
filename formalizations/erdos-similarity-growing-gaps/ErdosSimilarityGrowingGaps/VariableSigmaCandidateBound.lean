import ErdosSimilarityGrowingGaps.VariableQBounds

namespace ErdosSimilarityGrowingGaps

/-! With the geometric width set to `3*K`, the uniform quotient budget is
bounded by the total endpoint scale.  This is the scale separation needed by
the variable schedule; the final density parameter does not enter this
estimate. -/
theorem variableNodeUniformBudget_threeK_le
    {K : ℕ} (hK : 2 ≤ K) (U V D : ℝ)
    (hU : 3 ≤ U) (hUV : U ≤ V) (hD0 : 0 ≤ D)
    (hD : D ≤ (K : ℝ) * U) :
    (variableNodeUniformBudget K V D (3 * (K : ℝ)) : ℝ) + 1 ≤ V + 2 := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hV : 0 ≤ V := by linarith
  have harg : 0 ≤ (V / (1 / (K : ℝ)) + D) / (3 * (K : ℝ)) := by
    positivity
  have hKne : (K : ℝ) ≠ 0 := ne_of_gt hKpos
  have hscale : V / (1 / (K : ℝ)) = (K : ℝ) * V := by
    field_simp [hKne]
  have hquot : (V / (1 / (K : ℝ)) + D) / (3 * (K : ℝ)) ≤
      (2 / 3 : ℝ) * V := by
    rw [hscale]
    have hmul := mul_le_mul_of_nonneg_right hUV (by positivity : (0 : ℝ) ≤ 1 / 3)
    have hD' : D / (3 * (K : ℝ)) ≤ U / 3 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (K : ℝ))).2
      nlinarith [hD]
    field_simp [hKne]
    nlinarith [hmul, hD']
  have hceil := Nat.ceil_lt_add_one (show
      0 ≤ max ((V / (1 / (K : ℝ)) + D) / (3 * (K : ℝ))) 0 + 1 by positivity)
  dsimp [variableNodeUniformBudget]
  rw [max_eq_left harg] at hceil ⊢
  have hq : ((V / (1 / (K : ℝ)) + D) / (3 * (K : ℝ))) + 3 ≤ V + 2 := by
    nlinarith [hquot, hU]
  nlinarith [hceil, hq]

theorem variableNodeUniformBudget_threeK_candidate_count
    {M K : ℕ} (hK : 2 ≤ K) (U V D : ℝ)
    (hU : 3 ≤ U) (hUV : U ≤ V) (hD0 : 0 ≤ D)
    (hD : D ≤ (K : ℝ) * U) :
    (((M - 1) * (variableNodeUniformBudget K V D (3 * (K : ℝ)) + 1) : ℕ) : ℝ) ≤
      (M : ℝ) * (V + 2) := by
  have hQ := variableNodeUniformBudget_threeK_le hK U V D hU hUV hD0 hD
  have hM : 0 ≤ (M : ℝ) := by positivity
  have hsub : (((M - 1 : ℕ) : ℝ)) ≤ (M : ℝ) := by
    exact_mod_cast (Nat.sub_le M 1)
  have hmul := mul_le_mul hsub hQ (by positivity) hM
  calc
    (((M - 1) * (variableNodeUniformBudget K V D (3 * (K : ℝ)) + 1) : ℕ) : ℝ) =
        (((M - 1 : ℕ) : ℝ) *
          ((variableNodeUniformBudget K V D (3 * (K : ℝ)) + 1 : ℕ) : ℝ)) := by
      norm_num [Nat.cast_mul, Nat.cast_add]
    _ ≤ (M : ℝ) * (V + 2) := by
      norm_num [Nat.cast_add, Nat.cast_one] at hmul ⊢
      exact hmul

end ErdosSimilarityGrowingGaps
