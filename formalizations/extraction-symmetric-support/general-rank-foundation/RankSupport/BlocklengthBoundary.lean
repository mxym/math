import RankSupport.ExponentialLower

open scoped BigOperators
open Matrix Module

namespace ExtractionRankSupport

open SymmetricSupport

noncomputable section

theorem coordinateWordEmbedding_refl (D k : ℕ) :
    coordinateWordEmbedding (D := D) k (le_refl D) = Function.Embedding.refl (Word D k) := by
  ext w i
  rfl

theorem productVector_basis_word (D k : ℕ) (w : Word D k) :
    productVector D k (fun i => Pi.single (w i) (1 : ℂ)) =
      (1 : Matrix (Word D k) (Word D k) ℂ).col w := by
  have hC : Extraction.coordinateIsometry (coordinateWordEmbedding (D := D) k (le_refl D)) =
      (1 : Matrix (Word D k) (Word D k) ℂ) := by
    rw [coordinateWordEmbedding_refl]
    ext u v
    rfl
  have h := coordinate_productVector_eq_isometry_col D k D (le_refl D) w
  rw [hC] at h
  exact h

/-- If the blocklength itself is at most s, every tensor word already uses
at most s one-copy directions, so the intrinsic support is the entire space. -/
theorem rankBudgetProjector_eq_one_of_blocklength_le (D k s : ℕ) (hk : k ≤ s) :
    rankBudgetProjector D k s = 1 := by
  classical
  have h : rankBudgetProjector D k s * (1 : Matrix (Word D k) (Word D k) ℂ) = 1 := by
    apply matrix_mul_eq_of_fixes_columns
    intro w
    rw [← productVector_basis_word]
    apply rankBudgetProjector_fixes
    apply productVector_mem_rankBudgetSpace
    have hb : Module.finrank ℂ (Submodule.span ℂ
        (Set.range (fun i : Fin k => (Pi.single (w i) (1 : ℂ) : Fin D → ℂ)))) ≤ k := by
      simpa only [Set.finrank, Fintype.card_fin] using
        finrank_range_le_card (fun i : Fin k => (Pi.single (w i) (1 : ℂ) : Fin D → ℂ))
    exact hb.trans hk
  simpa only [Matrix.mul_one] using h

end
end ExtractionRankSupport
