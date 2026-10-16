import RankSupport.Basic
import MatrixSubspace
import Spectrum.Tensor

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionRankSupport

open SymmetricSupport ExtractionSpectrum

noncomputable section

/-- Every actual tensor-power column belongs to the intrinsic rank-budget
space. No spectral basis or Schur dimension formula is assumed. -/
theorem tensorMatrix_col_mem_rankBudgetSpace (D k s : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.rank ≤ s) (w : Word D k) :
    (tensorMatrix X k).col w ∈ rankBudgetSpace D k s := by
  let z : Fin k → Fin D → ℂ := fun i => X.col (w i)
  have hle : Submodule.span ℂ (Set.range z) ≤ LinearMap.range X.mulVecLin := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_mono
    rintro v ⟨i, rfl⟩
    exact ⟨w i, rfl⟩
  have hz : Module.finrank ℂ (Submodule.span ℂ (Set.range z)) ≤ s :=
    (Submodule.finrank_mono hle).trans hX
  change productVector D k z ∈ rankBudgetSpace D k s
  exact productVector_mem_rankBudgetSpace D k s z hz

/-- The actual orthogonal projector of the intrinsic space is constructed by
the finite basis/Gram-inverse factory. Its rank is proved, rather than supplied
as data in a support certificate. -/
def rankBudgetProjector (D k s : ℕ) : Matrix (Word D k) (Word D k) ℂ :=
  Classical.choose (MatrixSubspace.exists_subspace_projection (rankBudgetSpace D k s))

theorem rankBudgetProjector_properties (D k s : ℕ) :
    (rankBudgetProjector D k s).IsHermitian ∧
    rankBudgetProjector D k s * rankBudgetProjector D k s = rankBudgetProjector D k s ∧
    LinearMap.range (rankBudgetProjector D k s).mulVecLin = rankBudgetSpace D k s ∧
    (rankBudgetProjector D k s).rank = Module.finrank ℂ (rankBudgetSpace D k s) ∧
    ∀ v ∈ rankBudgetSpace D k s, rankBudgetProjector D k s *ᵥ v = v :=
  Classical.choose_spec (MatrixSubspace.exists_subspace_projection (rankBudgetSpace D k s))

theorem rankBudgetProjector_isHermitian (D k s : ℕ) :
    (rankBudgetProjector D k s).IsHermitian := (rankBudgetProjector_properties D k s).1

theorem rankBudgetProjector_idempotent (D k s : ℕ) :
    rankBudgetProjector D k s * rankBudgetProjector D k s = rankBudgetProjector D k s :=
  (rankBudgetProjector_properties D k s).2.1

theorem rankBudgetProjector_range (D k s : ℕ) :
    LinearMap.range (rankBudgetProjector D k s).mulVecLin = rankBudgetSpace D k s :=
  (rankBudgetProjector_properties D k s).2.2.1

theorem rankBudgetProjector_rank (D k s : ℕ) :
    (rankBudgetProjector D k s).rank = Module.finrank ℂ (rankBudgetSpace D k s) :=
  (rankBudgetProjector_properties D k s).2.2.2.1

theorem rankBudgetProjector_fixes (D k s : ℕ) (v : Word D k → ℂ)
    (hv : v ∈ rankBudgetSpace D k s) : rankBudgetProjector D k s *ᵥ v = v :=
  (rankBudgetProjector_properties D k s).2.2.2.2 v hv

theorem rankBudgetProjector_posSemidef (D k s : ℕ) :
    (rankBudgetProjector D k s).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (rankBudgetProjector D k s)
  rwa [(rankBudgetProjector_isHermitian D k s).eq,
    rankBudgetProjector_idempotent] at h

theorem matrix_mul_eq_of_fixes_columns {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P X : Matrix ι ι ℂ) (h : ∀ w, P *ᵥ X.col w = X.col w) : P * X = X := by
  ext v w
  simpa only [Matrix.mulVec, dotProduct, Matrix.col, Matrix.transpose_apply,
    Matrix.mul_apply] using congrFun (h w) v

/-- Genuine support for every original-coordinate tensor matrix of rank at
most s, without a PSD or density premise. -/
theorem rankBudgetProjector_mul_tensorMatrix (D k s : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.rank ≤ s) :
    rankBudgetProjector D k s * tensorMatrix X k = tensorMatrix X k := by
  apply matrix_mul_eq_of_fixes_columns
  intro w
  exact rankBudgetProjector_fixes D k s _
    (tensorMatrix_col_mem_rankBudgetSpace D k s X hX w)

theorem tensorMatrix_mul_rankBudgetProjector (D k s : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.rank ≤ s) (hH : X.IsHermitian) :
    tensorMatrix X k * rankBudgetProjector D k s = tensorMatrix X k := by
  have h := congrArg Matrix.conjTranspose (rankBudgetProjector_mul_tensorMatrix D k s X hX)
  have hTH : (tensorMatrix X k)ᴴ = tensorMatrix X k := by
    rw [← tensorMatrix_conjTranspose, hH.eq]
  simpa only [Matrix.conjTranspose_mul, hTH,
    (rankBudgetProjector_isHermitian D k s).eq] using h

theorem rankBudgetProjector_tensorMatrix_support (D k s : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.rank ≤ s) (hH : X.IsHermitian) :
    rankBudgetProjector D k s * tensorMatrix X k * rankBudgetProjector D k s =
      tensorMatrix X k := by
  rw [rankBudgetProjector_mul_tensorMatrix D k s X hX,
    tensorMatrix_mul_rankBudgetProjector D k s X hX hH]

/-- Actual tensor density and actual common support are derived together. -/
theorem rankBudgetProjector_density_support (D k s : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (hX : X.PosSemidef ∧ X.trace = 1)
    (hRank : X.rank ≤ s) :
    (tensorMatrix X k).PosSemidef ∧ (tensorMatrix X k).trace = 1 ∧
      rankBudgetProjector D k s * tensorMatrix X k * rankBudgetProjector D k s =
        tensorMatrix X k :=
  ⟨(tensorMatrix_density X hX k).1, (tensorMatrix_density X hX k).2,
    rankBudgetProjector_tensorMatrix_support D k s X hRank hX.1.isHermitian⟩

/-- The general intrinsic construction recovers the explicit, counted pure
support. In particular no extra Schur component is silently included at s=1. -/
theorem rankBudgetProjector_one_eq_symmetricProjector (D k : ℕ) :
    rankBudgetProjector D k 1 = symmetricProjector D k := by
  have hQP : rankBudgetProjector D k 1 * symmetricProjector D k =
      symmetricProjector D k := by
    apply matrix_mul_eq_of_fixes_columns
    intro w
    apply rankBudgetProjector_fixes
    rw [rankBudgetSpace_one_eq_symmetric_range, Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨w, rfl⟩
  have hPQ : symmetricProjector D k * rankBudgetProjector D k 1 =
      rankBudgetProjector D k 1 := by
    apply matrix_mul_eq_of_fixes_columns
    intro w
    have hw : (rankBudgetProjector D k 1).col w ∈ rankBudgetSpace D k 1 := by
      rw [← rankBudgetProjector_range, Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨w, rfl⟩
    rw [rankBudgetSpace_one_eq_symmetric_range] at hw
    obtain ⟨v, hv⟩ := hw
    change symmetricProjector D k *ᵥ _ = _
    rw [← hv]
    change symmetricProjector D k *ᵥ (symmetricProjector D k *ᵥ v) =
      symmetricProjector D k *ᵥ v
    rw [Matrix.mulVec_mulVec, symmetricProjector_idempotent]
  have hQP' := congrArg Matrix.conjTranspose hQP
  have heq : symmetricProjector D k * rankBudgetProjector D k 1 =
      symmetricProjector D k := by
    simpa only [Matrix.conjTranspose_mul, (symmetricProjector_hermitian D k).eq,
      (rankBudgetProjector_isHermitian D k 1).eq] using hQP'
  exact hPQ.symm.trans heq

theorem rankBudgetProjector_eq_one_of_dimension_le (D k s : ℕ) (hs : D ≤ s) :
    rankBudgetProjector D k s = 1 := by
  have hRank : (1 : Matrix (Fin D) (Fin D) ℂ).rank ≤ s := by
    simpa only [Matrix.rank_one, Fintype.card_fin] using hs
  have h := rankBudgetProjector_mul_tensorMatrix D k s 1 hRank
  simpa only [tensorMatrix_one, Matrix.mul_one] using h

end
end ExtractionRankSupport
