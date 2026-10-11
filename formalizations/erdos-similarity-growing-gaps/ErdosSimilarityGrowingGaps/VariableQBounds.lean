import ErdosSimilarityGrowingGaps.SequenceFiniteBlocker

namespace ErdosSimilarityGrowingGaps

/-! The bounded witness uses a child-dependent quotient.  It does not cancel
to a child-independent expression: the first denominator is `1/K`, while the
second is `K`.  The following upper envelope is the form useful for choosing
one common ceiling budget. -/
theorem variableRateNode_q_argument_le
    {K : ℕ} (hK : 0 < K) (u ell D δ : ℝ) (k : ℤ) (hδ : 0 < δ)
    (huk : 0 ≤ u + (k : ℝ)) :
    ((u + ell + (k : ℝ)) / (1 / (K : ℝ)) -
      ((u + (k : ℝ)) / (K : ℝ) - D)) / δ ≤
      ((u + ell + (k : ℝ)) / (1 / (K : ℝ)) + D) / δ := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hnonneg : 0 ≤ (u + (k : ℝ)) / (K : ℝ) := by
    exact div_nonneg huk hKreal.le
  have hraw : (u + ell + (k : ℝ)) / (1 / (K : ℝ)) -
      ((u + (k : ℝ)) / (K : ℝ) - D) ≤
      (u + ell + (k : ℝ)) / (1 / (K : ℝ)) + D := by
    linarith
  exact (div_le_div_iff_of_pos_right hδ).2 hraw

theorem variableRateNode_q_argument_le_of_upper
    {K : ℕ} (hK : 0 < K) (u ell D δ V : ℝ) (k : ℤ) (hδ : 0 < δ)
    (huk : 0 ≤ u + (k : ℝ))
    (hupper : u + ell + (k : ℝ) ≤ V) :
    ((u + ell + (k : ℝ)) / (1 / (K : ℝ)) -
      ((u + (k : ℝ)) / (K : ℝ) - D)) / δ ≤
      (V / (1 / (K : ℝ)) + D) / δ := by
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hden : 0 < (1 / (K : ℝ)) := by positivity
  have hscale : (u + ell + (k : ℝ)) / (1 / (K : ℝ)) ≤
      V / (1 / (K : ℝ)) :=
    (div_le_div_iff_of_pos_right hden).2 hupper
  have hlocal := variableRateNode_q_argument_le hK u ell D δ k hδ huk
  have hright0 : (u + ell + (k : ℝ)) / (1 / (K : ℝ)) + D ≤
      V / (1 / (K : ℝ)) + D := by
    nlinarith [hscale]
  have hright := (div_le_div_iff_of_pos_right hδ).2 hright0
  exact hlocal.trans hright

noncomputable def variableNodeUniformBudget
    (K : ℕ) (V D δ : ℝ) : ℕ :=
  Nat.ceil (max ((V / (1 / (K : ℝ)) + D) / δ) 0 + 1)

theorem variableNodeUniformBudget_spec
    (K : ℕ) (V D δ : ℝ) :
    max ((V / (1 / (K : ℝ)) + D) / δ) 0 + 1 ≤
      (variableNodeUniformBudget K V D δ : ℝ) := by
  dsimp [variableNodeUniformBudget]
  exact Nat.le_ceil _

theorem variableNodeUniformBudget_child_bound
    {M K : ℕ} (hK : 0 < K) (u : Fin (M - 1) → ℝ)
    (ell D δ V : ℝ) (k : ℤ) (hδ : 0 < δ)
    (huk : ∀ child, 0 ≤ u child + (k : ℝ))
    (hupper : ∀ child, u child + ell + (k : ℝ) ≤ V) :
    ∀ child, max (((u child + ell + (k : ℝ)) /
      (1 / (K : ℝ)) - ((u child + (k : ℝ)) / (K : ℝ) - D)) / δ) 0 + 1 ≤
      (variableNodeUniformBudget K V D δ : ℝ) := by
  intro child
  have hq := variableRateNode_q_argument_le_of_upper hK
    (u child) ell D δ V k hδ (huk child) (hupper child)
  have hmax : max (((u child + ell + (k : ℝ)) /
      (1 / (K : ℝ)) - ((u child + (k : ℝ)) / (K : ℝ) - D)) / δ) 0 ≤
      max ((V / (1 / (K : ℝ)) + D) / δ) 0 :=
    max_le_max hq le_rfl
  calc
    max (((u child + ell + (k : ℝ)) /
      (1 / (K : ℝ)) - ((u child + (k : ℝ)) / (K : ℝ) - D)) / δ) 0 + 1 ≤
        max ((V / (1 / (K : ℝ)) + D) / δ) 0 + 1 :=
      by nlinarith [hmax]
    _ ≤ (variableNodeUniformBudget K V D δ : ℝ) :=
      variableNodeUniformBudget_spec K V D δ

end ErdosSimilarityGrowingGaps
