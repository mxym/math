import RankSupport.PolynomialBound

open scoped BigOperators
open Matrix Module

namespace ExtractionRankSupport

open SymmetricSupport

noncomputable section

theorem rectangularTensor_col_mem_rankBudgetSpace {D s k : ℕ}
    (A : Matrix (Fin D) (Fin s) ℂ) (v : Word s k) :
    (rectangularTensor D s k A).col v ∈ rankBudgetSpace D k s := by
  let z : Fin k → Fin D → ℂ := fun i => A.col (v i)
  have hle : Submodule.span ℂ (Set.range z) ≤ Submodule.span ℂ (Set.range A.col) := by
    apply Submodule.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨v i, rfl⟩
  have hr : Module.finrank ℂ (Submodule.span ℂ (Set.range A.col)) ≤ s := by
    simpa only [Set.finrank, Fintype.card_fin] using finrank_range_le_card A.col
  change productVector D k z ∈ rankBudgetSpace D k s
  exact productVector_mem_rankBudgetSpace D k s z ((Submodule.finrank_mono hle).trans hr)

theorem rectangularColumnSpace_le_rankBudgetSpace {D s k : ℕ} (v : Word s k) :
    rectangularColumnSpace (D := D) v ≤ rankBudgetSpace D k s := by
  apply Submodule.map_le_iff_le_comap.mpr
  rw [symmetricProjector_range_eq_purePower_span]
  apply Submodule.span_le.mpr
  rintro f ⟨q, rfl⟩
  let A : Matrix (Fin D) (Fin s) ℂ := fun a b => q ((rectangularEntryEquiv D s).symm (a,b))
  have hA : rectangularEntryVector A = q := by
    ext i
    simp [rectangularEntryVector, A]
  change rectangularContraction v (purePower (D*s) k q) ∈ rankBudgetSpace D k s
  rw [← hA, rectangularContraction_purePower]
  exact rectangularTensor_col_mem_rankBudgetSpace A v

/-- An exact polynomial-coordinate identification of the actual support,
before introducing any Young diagram or representation-theoretic dimension. -/
theorem rankBudgetSpace_eq_rectangularUniversalSpace (D k s : ℕ) :
    rankBudgetSpace D k s = rectangularUniversalSpace D k s := by
  apply le_antisymm (rankBudgetSpace_le_rectangularUniversalSpace D k s)
  apply Finset.sup_le
  intro v _
  exact rectangularColumnSpace_le_rankBudgetSpace v

/-- A completely explicit finite coefficient matrix of the general support.
Its entries are the previously constructed occupation projector entries. -/
def supportCoefficientMatrix (D k s : ℕ) :
    Matrix (Word D k) (Word s k × Word (D*s) k) ℂ :=
  fun w j => symmetricProjector (D*s) k (rectangularPairWord w j.1) j.2

theorem supportCoefficientMatrix_range (D k s : ℕ) :
    LinearMap.range (supportCoefficientMatrix D k s).mulVecLin = rankBudgetSpace D k s := by
  classical
  apply le_antisymm
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro f ⟨⟨v,t⟩, rfl⟩
    apply rectangularColumnSpace_le_rankBudgetSpace v
    refine ⟨(symmetricProjector (D*s) k).col t, ?_, rfl⟩
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨t, rfl⟩
  · rw [rankBudgetSpace_eq_rectangularUniversalSpace D k s]
    apply Finset.sup_le
    intro v _
    rintro f ⟨g, ⟨x, hx⟩, rfl⟩
    rw [← hx]
    have he : rectangularContraction v ((symmetricProjector (D*s) k) *ᵥ x) =
        ∑ t, x t • (supportCoefficientMatrix D k s).col (v,t) := by
      ext w
      simp only [rectangularContraction, Matrix.mulVec, dotProduct, supportCoefficientMatrix,
        Matrix.col, Matrix.transpose_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro t _
      exact mul_comm _ _
    change rectangularContraction v ((symmetricProjector (D*s) k) *ᵥ x) ∈
      LinearMap.range (supportCoefficientMatrix D k s).mulVecLin
    rw [he]
    apply Submodule.sum_mem
    intro t _
    apply Submodule.smul_mem
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨(v,t), rfl⟩

/-- Exact finite rank computation reduces to one explicit coefficient matrix.
This is not the missing closed Schur/Weyl counting formula. -/
theorem rankBudgetProjector_rank_eq_coefficientMatrix_rank (D k s : ℕ) :
    (rankBudgetProjector D k s).rank = (supportCoefficientMatrix D k s).rank := by
  rw [rankBudgetProjector_rank]
  change _ = Module.finrank ℂ (LinearMap.range (supportCoefficientMatrix D k s).mulVecLin)
  rw [supportCoefficientMatrix_range]

end
end ExtractionRankSupport
