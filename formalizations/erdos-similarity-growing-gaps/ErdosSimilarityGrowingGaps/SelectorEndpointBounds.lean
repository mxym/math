import ErdosSimilarityGrowingGaps.RoutingTreeBounds
import ErdosSimilarityGrowingGaps.VariableQBounds

namespace ErdosSimilarityGrowingGaps

/-! Exact endpoint consequences for selector grids.

The global tree bound is stated in the convenient successor form
`selectorEnd + 1 ≤ origin + span`.  The finite-grid layer needs the
corresponding predecessor bound and, after casting, a real inequality.  These
lemmas are purely arithmetic; they do not add any probabilistic assumption.
-/

theorem selectorEnd_le_origin_add_span_sub_one
    {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (e : SelectorEdge M d) :
    c.selectorEnd e ≤ c.origin +
      RoutingTemplate.span M c.gap c.baseLength d - 1 := by
  have h := selectorEnd_global_bound c hM hL e
  omega

theorem selectorEnd_add_three_le_origin_add_span_add_two
    {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (e : SelectorEdge M d) :
    c.selectorEnd e + 3 ≤ c.origin +
      RoutingTemplate.span M c.gap c.baseLength d + 2 := by
  have h := selectorEnd_global_bound c hM hL e
  omega

theorem selectorEnd_cast_le_origin_add_span_sub_one
    {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (e : SelectorEdge M d) :
    (c.selectorEnd e : ℝ) ≤ (c.origin : ℝ) +
      (RoutingTemplate.span M c.gap c.baseLength d : ℝ) - 1 := by
  have h := selectorEnd_global_bound c hM hL e
  have h' : (c.selectorEnd e : ℝ) + 1 ≤
      (c.origin : ℝ) + (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by
    exact_mod_cast h
  linarith

theorem selector_grid_exponent_le_origin_add_span_add_two
    {M d : ℕ} (c : RoutingTemplate M d)
    (hM : 0 < M) (hL : 0 < c.baseLength) (e : SelectorEdge M d) :
    (c.selectorEnd e + 3 : ℕ) ≤ c.origin +
      RoutingTemplate.span M c.gap c.baseLength d + 2 := by
  exact selectorEnd_add_three_le_origin_add_span_add_two c hM hL e

/-! A direct candidate-count bridge for the separated local spacing
`σ = 3K`.  The final density parameter never enters this estimate. -/
theorem variable_uniform_candidate_count_le_endpoint
    {M K : ℕ} (hK : 2 ≤ K) (σ D V T : ℝ)
    (hσ : 3 * (K : ℝ) ≤ σ) (hD : 0 ≤ D) (hDle : D ≤ V)
    (hV : 6 ≤ V) (hVle : V ≤ T) :
    (((M - 1) * (variableNodeUniformBudget K V D σ + 1) : ℕ) : ℝ) ≤
      (M : ℝ) * T := by
  have hKpos : (0 : ℝ) < K := by
    exact_mod_cast (show 0 < K by omega)
  have hσpos : 0 < σ := lt_of_lt_of_le (by positivity) hσ
  have harg : 0 ≤ (V / (1 / (K : ℝ)) + D) / σ := by positivity
  have hceil := Nat.ceil_lt_add_one (show 0 ≤ max
      ((V / (1 / (K : ℝ)) + D) / σ) 0 + 1 by positivity)
  have hQ : (variableNodeUniformBudget K V D σ : ℝ) + 1 ≤ V := by
    dsimp [variableNodeUniformBudget] at hceil ⊢
    rw [max_eq_left harg] at hceil ⊢
    have hqcast : ((Nat.ceil ((V / (1 / (K : ℝ)) + D) / σ + 1) : ℕ) : ℝ)
        < (V / (1 / (K : ℝ)) + D) / σ + 2 := by linarith
    have hscale : V / (1 / (K : ℝ)) = (K : ℝ) * V := by
      field_simp [ne_of_gt hKpos]
    rw [hscale] at hqcast
    have hden : 0 < σ := hσpos
    have hnum : (K : ℝ) * V + D ≤ σ * (V - 3) := by
      have hσV : 3 * (K : ℝ) * (V - 3) ≤ σ * (V - 3) := by
        have := mul_le_mul_of_nonneg_right hσ (by linarith : 0 ≤ V - 3)
        simpa [mul_assoc] using this
      have hKreal : (2 : ℝ) ≤ K := by exact_mod_cast hK
      have hcore : (K : ℝ) * V + V ≤ 3 * (K : ℝ) * (V - 3) := by
        have hprod : 0 ≤ (2 * (K : ℝ) - 1) * (V - 6) := by
          have hfactor : 0 ≤ 2 * (K : ℝ) - 1 := by linarith
          have hVfactor : 0 ≤ V - 6 := by linarith
          exact mul_nonneg hfactor hVfactor
        nlinarith
      have hKV : (K : ℝ) * V + D ≤ (K : ℝ) * V + V := by linarith
      nlinarith [hσV, hcore, hKV]
    have hfrac : ((K : ℝ) * V + D) / σ ≤ V - 3 :=
      (div_le_iff₀ hden).2 (by simpa [mul_comm] using hnum)
    have harg' : ((K : ℝ) * V + D) / σ + 2 ≤ V - 1 := by linarith
    have hqcast' : ((Nat.ceil (((K : ℝ) * V + D) / σ + 1) : ℕ) : ℝ) <
        V - 1 := by simpa [hscale, div_eq_mul_inv] using hqcast.trans_le harg'
    rw [hscale]
    linarith
  have hcount : (((M - 1 : ℕ) : ℝ)) ≤ (M : ℝ) := by
    exact_mod_cast (Nat.sub_le M 1)
  have hMnonneg : 0 ≤ (M : ℝ) := by positivity
  have hprod := mul_le_mul hcount hQ (by positivity) hMnonneg
  calc
    (((M - 1) * (variableNodeUniformBudget K V D σ + 1) : ℕ) : ℝ) =
        (((M - 1 : ℕ) : ℝ) *
          ((variableNodeUniformBudget K V D σ + 1 : ℕ) : ℝ)) := by
      norm_num [Nat.cast_mul]
    _ ≤ (M : ℝ) * V := by simpa only [Nat.cast_add, Nat.cast_one] using hprod
    _ ≤ (M : ℝ) * T := mul_le_mul_of_nonneg_left hVle hMnonneg

theorem variable_uniform_candidate_count_of_template
    {M K d : ℕ} (hK : 2 ≤ K) (c : RoutingTemplate M d)
    (σ D : ℝ) (hσ : 3 * (K : ℝ) ≤ σ) (hD : 0 ≤ D)
    (horigin : 4 ≤ c.origin)
    (hspan : (RoutingTemplate.span M c.gap c.baseLength d : ℝ) ≤ c.origin)
    (hcoeff : |(k : ℝ)| ≤ c.origin) (hDorigin : D ≤ (c.origin : ℝ)) :
    (((M - 1) * (variableNodeUniformBudget K
      ((c.origin : ℝ) + RoutingTemplate.span M c.gap c.baseLength d +
        |(k : ℝ)| + 2) D σ + 1) : ℕ) : ℝ) ≤
      (M : ℝ) * ((c.origin : ℝ) +
        (RoutingTemplate.span M c.gap c.baseLength d : ℝ) + |(k : ℝ)| + 2) := by
  let T : ℝ := (c.origin : ℝ) +
    (RoutingTemplate.span M c.gap c.baseLength d : ℝ) + |(k : ℝ)| + 2
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hT6 : 6 ≤ T := by
    dsimp [T]
    have ho : (4 : ℝ) ≤ c.origin := by exact_mod_cast horigin
    have hs : 0 ≤ (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by positivity
    have hk : 0 ≤ |(k : ℝ)| := abs_nonneg _
    linarith
  have hDle : D ≤ T := by
    dsimp [T]
    have hs : 0 ≤ (RoutingTemplate.span M c.gap c.baseLength d : ℝ) := by positivity
    have hk : 0 ≤ |(k : ℝ)| := abs_nonneg _
    linarith [hDorigin]
  apply variable_uniform_candidate_count_le_endpoint hK σ D T T hσ hD hDle
    hT6 le_rfl

end ErdosSimilarityGrowingGaps
