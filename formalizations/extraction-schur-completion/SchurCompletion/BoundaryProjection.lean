import SchurCompletion.FirstColumnBoundary

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

/-- Before the first excluded column, the actual intrinsic support is full. -/
theorem rankBudgetSpace_eq_top_of_blocklength_le (D k s : ℕ) (hks : k ≤ s) :
    rankBudgetSpace D k s = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℂ (Word D k)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨w,rfl⟩
  rw [Pi.basisFun_apply,← productVector_basis D k w]
  apply Submodule.subset_span
  refine ⟨_,?_,rfl⟩
  apply le_trans _ hks
  simpa only [Set.finrank,Fintype.card_fin] using
    (finrank_range_le_card (R := ℂ) (fun j : Fin k => (Pi.single (w j) 1 : Fin D → ℂ)))

theorem rankBudgetProjector_eq_one_of_blocklength_le (D k s : ℕ) (hks : k ≤ s) :
    rankBudgetProjector D k s = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change rankBudgetProjector D k s *ᵥ v = (1 : Matrix (Word D k) (Word D k) ℂ) *ᵥ v
  rw [Matrix.one_mulVec]
  apply rankBudgetProjector_fixes
  rw [rankBudgetSpace_eq_top_of_blocklength_le D k s hks]
  exact Submodule.mem_top

theorem coordinateWedgeMap_antisymmetrizer (D k : ℕ) (v : Word D k → ℂ) :
    coordinateWedgeMap D k (tensorAntisymmetrizer D k *ᵥ v) =
      (Fintype.card (Equiv.Perm (Fin k)) : ℂ) • coordinateWedgeMap D k v := by
  have hew := DFunLike.congr_fun (exteriorTensorEmbedding_coordinateWedgeMap D k) v
  change exteriorTensorEmbedding D k (coordinateWedgeMap D k v) =
    tensorAntisymmetrizer D k *ᵥ v at hew
  rw [← hew]
  exact DFunLike.congr_fun (coordinateWedgeMap_exteriorTensorEmbedding D k)
    (coordinateWedgeMap D k v)

theorem coordinateWedgeMap_complement_alternating (D k : ℕ) (v : Word D k → ℂ) :
    coordinateWedgeMap D k ((1-alternatingProjector D k) *ᵥ v) = 0 := by
  have hc : (Fintype.card (Equiv.Perm (Fin k)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Matrix.sub_mulVec,Matrix.one_mulVec,map_sub,alternatingProjector,
    Matrix.smul_mulVec,map_smul,coordinateWedgeMap_antisymmetrizer,← mul_smul,
    inv_mul_cancel₀ hc,one_smul,sub_self]

/-- Actual matrix classification at k=s+1: the rank-budget support projector
 is exactly the complement of the exterior-power projector. -/
theorem rankBudgetProjector_boundary_eq_complement (D s : ℕ) :
    rankBudgetProjector D (s+1) s = 1-alternatingProjector D (s+1) := by
  let P := rankBudgetProjector D (s+1) s
  let Q := alternatingProjector D (s+1)
  have hQP : Q*P = 0 := by
    simp only [Q,P,alternatingProjector,Matrix.smul_mul,
      tensorAntisymmetrizer_mul_rankBudgetProjector D (s+1) s (by omega),smul_zero]
  have hPQ : P*Q = 0 := by
    have h := congrArg Matrix.conjTranspose hQP
    simpa only [P,Q,Matrix.conjTranspose_mul,Matrix.conjTranspose_zero,
      (rankBudgetProjector_isHermitian D (s+1) s).eq,
      (alternatingProjector_hermitian D (s+1)).eq] using h
  have hFix : P*(1-Q) = 1-Q := by
    apply matrix_mul_eq_of_fixes_columns
    intro w
    apply rankBudgetProjector_fixes
    have hk := rankBudgetSpace_pred_eq_wedge_kernel D (s+1) (by omega)
    simp only [Nat.add_sub_cancel] at hk
    rw [hk]
    apply LinearMap.mem_ker.mpr
    have h := coordinateWedgeMap_complement_alternating D (s+1) (Pi.single w 1)
    simpa only [Matrix.mulVec_single_one,Matrix.col_apply] using h
  have hP : P*(1-Q) = P := by rw [Matrix.mul_sub,Matrix.mul_one,hPQ,sub_zero]
  exact hP.symm.trans hFix

end
end ExtractionSchur
