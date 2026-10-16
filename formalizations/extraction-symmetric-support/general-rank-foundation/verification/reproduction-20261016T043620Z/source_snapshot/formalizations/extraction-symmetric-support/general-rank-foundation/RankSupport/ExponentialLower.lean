import RankSupport.PolynomialBound
import Extraction.SubspacePacking

open scoped BigOperators
open Matrix Module

namespace ExtractionRankSupport

open SymmetricSupport

noncomputable section

def coordinateLetterEmbedding {D s : ℕ} (hs : s ≤ D) : Fin s ↪ Fin D where
  toFun a := ⟨a.val, a.isLt.trans_le hs⟩
  inj' a b h := by
    apply Fin.ext
    exact congrArg (fun x : Fin D => x.val) h

def coordinateWordEmbedding {D s : ℕ} (k : ℕ) (hs : s ≤ D) : Word s k ↪ Word D k where
  toFun w i := coordinateLetterEmbedding hs (w i)
  inj' _ _ h := funext fun i => (coordinateLetterEmbedding hs).injective (congrFun h i)

theorem coordinate_factors_finrank_le (D k s : ℕ) (hs : s ≤ D) (w : Word s k) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range
      (fun i : Fin k => (Pi.single (coordinateLetterEmbedding hs (w i)) (1 : ℂ) :
        Fin D → ℂ)))) ≤ s := by
  classical
  let b : Fin s → Fin D → ℂ := fun a => Pi.single (coordinateLetterEmbedding hs a) 1
  have hle : Submodule.span ℂ (Set.range (fun i => b (w i))) ≤
      Submodule.span ℂ (Set.range b) := by
    apply Submodule.span_mono
    rintro v ⟨i, rfl⟩
    exact ⟨w i, rfl⟩
  exact (Submodule.finrank_mono hle).trans
    (by simpa only [Set.finrank, Fintype.card_fin] using finrank_range_le_card b)

theorem coordinate_productVector_eq_isometry_col (D k s : ℕ) (hs : s ≤ D) (w : Word s k) :
    productVector D k (fun i => Pi.single (coordinateLetterEmbedding hs (w i)) (1 : ℂ)) =
      (Extraction.coordinateIsometry (coordinateWordEmbedding k hs)).col w := by
  classical
  ext u
  by_cases h : u = coordinateWordEmbedding k hs w
  · subst u
    simp only [Extraction.coordinateIsometry, Matrix.col, Matrix.transpose_apply,
      ite_true, eq_self_iff_true]
    change (∏ i, (Pi.single (coordinateLetterEmbedding hs (w i)) (1 : ℂ) : Fin D → ℂ)
      (coordinateLetterEmbedding hs (w i))) = (1 : ℂ)
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    change (∏ i, (Pi.single (coordinateLetterEmbedding hs (w i)) (1 : ℂ) : Fin D → ℂ) (u i)) =
      if u = coordinateWordEmbedding k hs w then (1 : ℂ) else 0
    rw [if_neg h]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change u i ≠ coordinateLetterEmbedding hs (w i) at hi
    simp [Pi.single_apply, hi]

/-- A fixed s-dimensional coordinate subspace supplies s^k independent actual
tensor vectors inside the intrinsic support. -/
theorem rankBudgetProjector_rank_ge_power (D k s : ℕ) (hs : s ≤ D) :
    s ^ k ≤ (rankBudgetProjector D k s).rank := by
  classical
  let C := Extraction.coordinateIsometry (coordinateWordEmbedding k hs)
  have hC : Cᴴ * C = 1 := Extraction.coordinateIsometry_isometry _
  have hlower : s ^ k ≤ C.rank := by
    have h := Matrix.rank_mul_le_right Cᴴ C
    rw [hC, Matrix.rank_one] at h
    simpa only [Word, Fintype.card_fun, Fintype.card_fin] using h
  have hRange : LinearMap.range C.mulVecLin ≤ rankBudgetSpace D k s := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro v ⟨w, rfl⟩
    rw [← coordinate_productVector_eq_isometry_col D k s hs w]
    exact productVector_mem_rankBudgetSpace D k s _
      (coordinate_factors_finrank_le D k s hs w)
  rw [rankBudgetProjector_rank]
  exact hlower.trans (Submodule.finrank_mono hRange)

end
end ExtractionRankSupport
