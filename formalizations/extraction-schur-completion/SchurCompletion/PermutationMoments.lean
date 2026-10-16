import SchurCompletion.RankCentralSupport

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem rectangularTensor_mul_conjTranspose (D s k : ℕ) (A : Matrix (Fin D) (Fin s) ℂ) :
    tensorMatrix (A*Aᴴ) k = rectangularTensor D s k A * (rectangularTensor D s k A)ᴴ := by
  ext w v
  simp only [tensorMatrix,Matrix.mul_apply,Matrix.conjTranspose_apply,rectangularTensor,star_prod]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact Finset.prod_mul_distrib

theorem rectangularTensor_coordinateIsometry (D s k : ℕ) (hsD : s ≤ D) :
    rectangularTensor D s k (Extraction.coordinateIsometry (coordinateLetterEmbedding hsD)) =
      Extraction.coordinateIsometry (coordinateWordEmbedding k hsD) := by
  ext w v
  by_cases h : w = coordinateWordEmbedding k hsD v
  · subst w
    simp only [rectangularTensor,Extraction.coordinateIsometry,ite_true]
    change (∏ i : Fin k, if coordinateLetterEmbedding hsD (v i) =
      coordinateLetterEmbedding hsD (v i) then (1 : ℂ) else 0) = 1
    simp
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    simp only [rectangularTensor,Extraction.coordinateIsometry,h,ite_false]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact if_neg hi

theorem flatCoordinateDensity_tensor_factor (D s k : ℕ) (hsD : s ≤ D) :
    tensorMatrix (flatCoordinateDensity D s hsD) k =
      ((s : ℝ)^k)⁻¹ •
        (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD) *
          (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD))ᴴ) := by
  rw [flatCoordinateDensity,normalizedProjection,coordinateRankProjection_rank,
    tensorMatrix_real_smul,inv_pow]
  rw [coordinateRankProjection,rectangularTensor_mul_conjTranspose,
    rectangularTensor_coordinateIsometry]

theorem copyPermutation_coordinateIsometry (D s k : ℕ) (hsD : s ≤ D)
    (σ : Equiv.Perm (Fin k)) :
    copyPermutationMatrix D k σ * Extraction.coordinateIsometry (coordinateWordEmbedding k hsD) =
      Extraction.coordinateIsometry (coordinateWordEmbedding k hsD) * copyPermutationMatrix s k σ := by
  unfold copyPermutationMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul,PEquiv.mul_toMatrix_toPEquiv]
  ext w v
  have heq : w ∘ σ = coordinateWordEmbedding k hsD v ↔
      w = coordinateWordEmbedding k hsD (v ∘ σ.symm) := by
    constructor
    · intro h
      apply funext
      intro i
      have hi := congrFun h (σ.symm i)
      change w (σ (σ.symm i)) = coordinateLetterEmbedding hsD (v (σ.symm i)) at hi
      change w i = coordinateLetterEmbedding hsD (v (σ.symm i))
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hi
    · intro h
      apply funext
      intro i
      have hi := congrFun h (σ i)
      change w (σ i) = coordinateLetterEmbedding hsD (v (σ.symm (σ i))) at hi
      change w (σ i) = coordinateLetterEmbedding hsD (v i)
      simpa only [Equiv.symm_apply_apply] using hi
  change (if w ∘ σ = coordinateWordEmbedding k hsD v then (1 : ℂ) else 0) =
    if w = coordinateWordEmbedding k hsD (v ∘ σ.symm) then 1 else 0
  simp only [heq]

def fixedWordCard (D k : ℕ) (σ : Equiv.Perm (Fin k)) : ℕ :=
  (Function.fixedPoints (positionWordEquiv D k σ)).ncard

theorem copyPermutation_trace (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (copyPermutationMatrix D k σ).trace = (fixedWordCard D k σ : ℂ) :=
  Matrix.trace_permutation _

/-- Literal finite-copy permutation character of the concrete flat density. -/
theorem flatCoordinateDensity_permutation_moment (D s k : ℕ) (hsD : s ≤ D)
    (σ : Equiv.Perm (Fin k)) :
    (copyPermutationMatrix D k σ * tensorMatrix (flatCoordinateDensity D s hsD) k).trace =
      ((s : ℝ)^k)⁻¹ • (fixedWordCard s k σ : ℂ) := by
  let C := Extraction.coordinateIsometry (coordinateWordEmbedding k hsD)
  have hC : Cᴴ*C = 1 := Extraction.coordinateIsometry_isometry _
  rw [flatCoordinateDensity_tensor_factor,Matrix.mul_smul,Matrix.trace_smul]
  congr 1
  change (copyPermutationMatrix D k σ * (C*Cᴴ)).trace = _
  rw [← Matrix.mul_assoc,copyPermutation_coordinateIsometry,Matrix.trace_mul_cycle]
  change (Cᴴ*C*copyPermutationMatrix s k σ).trace = _
  rw [hC,Matrix.one_mul,copyPermutation_trace]

theorem flatHaarAverage_permutation_moment (D s k : ℕ) (hsD : s ≤ D)
    (σ : Equiv.Perm (Fin k)) :
    (copyPermutationMatrix D k σ * flatHaarAverage D s k hsD).trace =
      ((s : ℝ)^k)⁻¹ • (fixedWordCard s k σ : ℂ) := by
  rw [flatHaarAverage,haarOrbitAverage_eq_haarTwirl,
    haarTwirl_pairing D k _ _ (Submodule.subset_span ⟨σ,rfl⟩)]
  exact flatCoordinateDensity_permutation_moment D s k hsD σ

/-- Exact Gram entries of actual copy-permutation matrices. -/
theorem copyPermutation_gram (D k : ℕ) (σ τ : Equiv.Perm (Fin k)) :
    ((copyPermutationMatrix D k σ)ᴴ * copyPermutationMatrix D k τ).trace =
      (fixedWordCard D k (σ⁻¹*τ) : ℂ) := by
  rw [copyPermutationMatrix_star,copyPermutationMatrix_mul,copyPermutation_trace]

end
end ExtractionSchur
