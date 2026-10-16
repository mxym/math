import RankSupport.TensorSupport

open scoped BigOperators
open Matrix

namespace ExtractionRankSupport

open SymmetricSupport ExtractionSpectrum

theorem tensorMatrix_mulVec_productVector (D k : ℕ)
    (M : Matrix (Fin D) (Fin D) ℂ) (z : Fin k → Fin D → ℂ) :
    tensorMatrix M k *ᵥ productVector D k z =
      productVector D k (fun i => M *ᵥ z i) := by
  ext w
  simp only [Matrix.mulVec, dotProduct, tensorMatrix, productVector]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact (Finset.prod_mul_distrib :
    (∏ i, M (w i) (v i) * z i (v i)) =
      (∏ i, M (w i) (v i)) * ∏ i, z i (v i)).symm

theorem transformed_factors_finrank_le (D k : ℕ)
    (M : Matrix (Fin D) (Fin D) ℂ) (z : Fin k → Fin D → ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (fun i => M *ᵥ z i))) ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range z)) := by
  have hle : Submodule.span ℂ (Set.range (fun i => M *ᵥ z i)) ≤
      (Submodule.span ℂ (Set.range z)).map M.mulVecLin := by
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    exact ⟨z i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_map_le _ _)

/-- The support is invariant under every actual identical one-copy linear
action. The unitary case is a consequence rather than an interface premise. -/
theorem tensorMatrix_preserves_rankBudgetSpace (D k s : ℕ)
    (M : Matrix (Fin D) (Fin D) ℂ) (v : Word D k → ℂ)
    (hv : v ∈ rankBudgetSpace D k s) :
    tensorMatrix M k *ᵥ v ∈ rankBudgetSpace D k s := by
  have hle : rankBudgetSpace D k s ≤
      (rankBudgetSpace D k s).comap (tensorMatrix M k).mulVecLin := by
    apply Submodule.span_le.mpr
    rintro v ⟨z, hz, rfl⟩
    change tensorMatrix M k *ᵥ productVector D k z ∈ rankBudgetSpace D k s
    rw [tensorMatrix_mulVec_productVector]
    exact productVector_mem_rankBudgetSpace D k s _
      ((transformed_factors_finrank_le D k M z).trans hz)
  exact hle hv

theorem rankBudgetProjector_tensorMatrix_compress (D k s : ℕ)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    rankBudgetProjector D k s * tensorMatrix M k * rankBudgetProjector D k s =
      tensorMatrix M k * rankBudgetProjector D k s := by
  rw [Matrix.mul_assoc]
  apply matrix_mul_eq_of_fixes_columns
  intro w
  have hcol : (tensorMatrix M k * rankBudgetProjector D k s).col w =
      tensorMatrix M k *ᵥ (rankBudgetProjector D k s).col w := by
    ext v
    rfl
  rw [hcol]
  apply rankBudgetProjector_fixes
  apply tensorMatrix_preserves_rankBudgetSpace
  rw [← rankBudgetProjector_range, Matrix.range_mulVecLin]
  exact Submodule.subset_span ⟨w, rfl⟩

/-- The intrinsic projector commutes with all actual tensor powers, including
singular linear actions, so in particular with U^⊗k. -/
theorem rankBudgetProjector_commutes_tensorMatrix (D k s : ℕ)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    rankBudgetProjector D k s * tensorMatrix M k =
      tensorMatrix M k * rankBudgetProjector D k s := by
  have h := congrArg Matrix.conjTranspose
    (rankBudgetProjector_tensorMatrix_compress D k s Mᴴ)
  have h' : rankBudgetProjector D k s * tensorMatrix M k * rankBudgetProjector D k s =
      rankBudgetProjector D k s * tensorMatrix M k := by
    simpa only [Matrix.conjTranspose_mul, ← tensorMatrix_conjTranspose,
      Matrix.conjTranspose_conjTranspose, (rankBudgetProjector_isHermitian D k s).eq,
      ← Matrix.mul_assoc] using h
  exact h'.symm.trans (rankBudgetProjector_tensorMatrix_compress D k s M)

end ExtractionRankSupport
