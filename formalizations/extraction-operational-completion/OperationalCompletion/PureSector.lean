import OperationalCompletion.UniversalSectors
import RankSupport.Invariance

open scoped BigOperators ComplexOrder
open Matrix SymmetricSupport UniversalOrbit ExtractionRankSupport
namespace OperationalCompletion
noncomputable section

theorem symmetric_range_le_universalSpace (D k : ℕ) (S : Finset (Word D k)) (hS : S.Nonempty) :
    LinearMap.range (symmetricProjector D k).mulVecLin≤universalSpace S := by
  obtain ⟨w,hw⟩ := hS
  rw [symmetricProjector_range_eq_purePower_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨z,rfl⟩
  let M : Matrix (Fin D) (Fin D) ℂ := fun i _ => z i
  have h := tensorAction_single_mem_universalSpace S w hw M
  have he : tensorAction M (Pi.single w (1:ℂ))=purePower D k z := by
    ext x
    simp [tensorAction,M,purePower,Pi.single_apply,mul_ite]
  rwa [he] at h

theorem universalProjection_contains_symmetric (D k : ℕ) (S : Finset (Word D k)) (hS : S.Nonempty) :
    symmetricProjector D k*universalProjection D k S=symmetricProjector D k ∧
    universalProjection D k S*symmetricProjector D k=symmetricProjector D k := by
  have h : universalProjection D k S*symmetricProjector D k=symmetricProjector D k := by
    apply mul_eq_of_fixes_columns
    intro w
    apply universalProjection_fixes
    apply symmetric_range_le_universalSpace D k S hS
    rw [Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨w,rfl⟩
  refine ⟨?_,h⟩
  have hc := congrArg Matrix.conjTranspose h
  simpa only [Matrix.conjTranspose_mul,(symmetricProjector_hermitian D k).eq,
    (universalProjection_hermitian D k S).eq] using hc

def nonsymmetricProjection (D k : ℕ) (S : Finset (Word D k)) : Matrix (Word D k) (Word D k) ℂ :=
  if S.Nonempty then universalProjection D k S-symmetricProjector D k else 0

theorem nonsymmetricProjection_hermitian (D k : ℕ) (S : Finset (Word D k)) :
    (nonsymmetricProjection D k S).IsHermitian := by
  unfold nonsymmetricProjection
  split
  · exact (universalProjection_hermitian D k S).sub (symmetricProjector_hermitian D k)
  · simp [Matrix.IsHermitian]

theorem nonsymmetricProjection_idempotent (D k : ℕ) (S : Finset (Word D k)) :
    nonsymmetricProjection D k S*nonsymmetricProjection D k S=nonsymmetricProjection D k S := by
  unfold nonsymmetricProjection
  split
  next hS =>
    exact projectionDifference_idempotent _ _ (symmetricProjector_idempotent D k)
      (universalProjection_idempotent D k S)
      (universalProjection_contains_symmetric D k S hS).1
      (universalProjection_contains_symmetric D k S hS).2
  next hS => simp

theorem nonsymmetricProjection_rank_le (D k : ℕ) (S : Finset (Word D k)) :
    (nonsymmetricProjection D k S).rank≤S.card*(D*D+k-1).choose k := by
  unfold nonsymmetricProjection
  split
  next hS =>
    exact (projectionDifference_rank_le _ _ (universalProjection_idempotent D k S)
      (universalProjection_contains_symmetric D k S hS).1).trans (universalProjection_rank_le D k S)
  next hS => simp

theorem nonsymmetricProjection_orthogonal_symmetric (D k : ℕ) (S : Finset (Word D k)) :
    symmetricProjector D k*nonsymmetricProjection D k S=0 ∧
      nonsymmetricProjection D k S*symmetricProjector D k=0 := by
  unfold nonsymmetricProjection
  split
  next hS =>
    have h := universalProjection_contains_symmetric D k S hS
    constructor
    · rw [mul_sub,h.1,symmetricProjector_idempotent,sub_self]
    · rw [sub_mul,h.2,symmetricProjector_idempotent,sub_self]
  next hS => simp

theorem nonsymmetricProjection_nested (D k : ℕ) (S T : Finset (Word D k)) (hST : S⊆T) :
    nonsymmetricProjection D k S*nonsymmetricProjection D k T=nonsymmetricProjection D k S ∧
      nonsymmetricProjection D k T*nonsymmetricProjection D k S=nonsymmetricProjection D k S := by
  by_cases hS : S.Nonempty
  · have hT : T.Nonempty := hS.mono hST
    have hnest := universalProjection_nested D k S T hST
    have hSymS := universalProjection_contains_symmetric D k S hS
    have hSymT := universalProjection_contains_symmetric D k T hT
    simp only [nonsymmetricProjection,if_pos hS,if_pos hT]
    constructor <;> simp only [sub_mul,mul_sub,hnest.1,hnest.2,hSymS.1,hSymS.2,
      hSymT.1,hSymT.2,symmetricProjector_idempotent] <;> abel
  · simp only [nonsymmetricProjection,if_neg hS,Matrix.zero_mul,Matrix.mul_zero]
    constructor <;> trivial

theorem symmetricProjector_commutes_tensorMatrix (D k : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    symmetricProjector D k*ExtractionSpectrum.tensorMatrix X k=
      ExtractionSpectrum.tensorMatrix X k*symmetricProjector D k := by
  simpa only [rankBudgetProjector_one_eq_symmetricProjector] using
    rankBudgetProjector_commutes_tensorMatrix D k 1 X

theorem nonsymmetricProjection_commutes_tensorMatrix (D k : ℕ) (S : Finset (Word D k))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    nonsymmetricProjection D k S*ExtractionSpectrum.tensorMatrix X k=
      ExtractionSpectrum.tensorMatrix X k*nonsymmetricProjection D k S := by
  unfold nonsymmetricProjection
  split
  · rw [sub_mul,mul_sub,universalProjection_commutes_tensor,symmetricProjector_commutes_tensorMatrix]
  · simp

end
end OperationalCompletion
