import ErdosSimilarityGrowingGaps.VariableQBounds

namespace ErdosSimilarityGrowingGaps

/-! A corrected, standalone candidate-count envelope.  The legacy certificate
stores the sharper `M * (origin + span + |k| + 2)` bound; when the quotient
budget is selected uniformly, the directly derivable envelope carries the
extra `K/δ` scale.  This theorem records a safe scaled alternative without
changing the legacy certificate structure. -/
theorem variable_uniform_candidate_count_le_scaled
    {M K : ℕ} (hK : 2 ≤ K) (δ D V : ℝ)
    (hδ : 0 < δ) (hD : 0 ≤ D) (hV : 1 ≤ V)
    (hMscale : (K : ℝ) / δ + D / δ + 3 ≤ (M : ℝ)) :
    (((M - 1) *
      (variableNodeUniformBudget K V D δ + 1) : ℕ) : ℝ) ≤
      (M : ℝ) ^ 2 * V := by
  have hKpos : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  have hden : 0 < (1 / (K : ℝ)) := by positivity
  have ht : 0 ≤ (V / (1 / (K : ℝ)) + D) / δ := by
    positivity
  have hceil := Nat.ceil_lt_add_one (show
      0 ≤ max ((V / (1 / (K : ℝ)) + D) / δ) 0 + 1 by positivity)
  have hQ : (variableNodeUniformBudget K V D δ : ℝ) + 1 ≤
      (K : ℝ) * V / δ + D / δ + 3 := by
    dsimp [variableNodeUniformBudget] at hceil ⊢
    have hmax : max ((V / (1 / (K : ℝ)) + D) / δ) 0 =
        (V / (1 / (K : ℝ)) + D) / δ := max_eq_left ht
    rw [hmax] at hceil ⊢
    have hqcast :
        ((Nat.ceil ((V / (1 / (K : ℝ)) + D) / δ + 1) : ℕ) : ℝ) <
          (V / (1 / (K : ℝ)) + D) / δ + 2 := by
      linarith [hceil]
    have hscale : V / (1 / (K : ℝ)) = (K : ℝ) * V := by
      field_simp [ne_of_gt hKpos]
    rw [hscale] at hqcast
    rw [hscale]
    have harg : ((K : ℝ) * V + D) / δ + 2 =
        (K : ℝ) * V / δ + D / δ + 2 := by ring
    rw [harg] at hqcast
    nlinarith
  have hKV : (K : ℝ) / δ * V + D / δ + 3 ≤ (M : ℝ) * V := by
    have hV0 : 0 ≤ V := by linarith
    have hmul := mul_le_mul_of_nonneg_right hMscale hV0
    calc
      (K : ℝ) / δ * V + D / δ + 3 ≤
          (K : ℝ) / δ * V + (D / δ) * V + 3 * V := by
            have hDδ : 0 ≤ D / δ := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hV hDδ,
              mul_le_mul_of_nonneg_left hV (by norm_num : (0 : ℝ) ≤ 3)]
      _ = ((K : ℝ) / δ + D / δ + 3) * V := by ring
      _ ≤ (M : ℝ) * V := hmul
  have hQ' : (variableNodeUniformBudget K V D δ : ℝ) + 1 ≤
      (M : ℝ) * V := by
    calc
      (variableNodeUniformBudget K V D δ : ℝ) + 1 ≤
          (K : ℝ) * V / δ + D / δ + 3 := hQ
      _ = (K : ℝ) / δ * V + D / δ + 3 := by ring
      _ ≤ (M : ℝ) * V := hKV
  have hMnonneg : 0 ≤ (M : ℝ) := by positivity
  have hcount : (((M - 1) : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (Nat.sub_le M 1)
  have hprod := mul_le_mul hcount hQ' (by positivity) hMnonneg
  have htarget : (M : ℝ) * ((M : ℝ) * V) = (M : ℝ) ^ 2 * V := by ring
  calc
    (((M - 1) * (variableNodeUniformBudget K V D δ + 1) : ℕ) : ℝ) =
        (((M - 1 : ℕ) : ℝ) *
          ((variableNodeUniformBudget K V D δ + 1 : ℕ) : ℝ)) := by
      norm_num [Nat.cast_mul]
    _ ≤ (M : ℝ) * ((M : ℝ) * V) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hprod
    _ = (M : ℝ) ^ 2 * V := htarget

end ErdosSimilarityGrowingGaps
