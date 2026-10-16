import SchurCompletion.HaarProjection
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

def productTensorMultilinear (D k : ℕ) :
    MultilinearMap ℂ (fun _ : Fin k => Fin D → ℂ) (Word D k → ℂ) :=
  MultilinearMap.pi (fun w : Word D k =>
    (MultilinearMap.mkPiAlgebra ℂ (Fin k) ℂ).compLinearMap
      (fun i => LinearMap.proj (w i)))

theorem productTensorMultilinear_apply (D k : ℕ) (z : Fin k → Fin D → ℂ) :
    productTensorMultilinear D k z = productVector D k z := rfl

def alternatingTensorMap (D k : ℕ) : (Fin D → ℂ) [⋀^Fin k]→ₗ[ℂ] (Word D k → ℂ) :=
  MultilinearMap.alternatization (productTensorMultilinear D k)

theorem alternatingTensorMap_rank_deficient (D k s : ℕ) (hsk : s < k)
    (z : Fin k → Fin D → ℂ)
    (hz : Module.finrank ℂ (Submodule.span ℂ (Set.range z)) ≤ s) :
    alternatingTensorMap D k z = 0 := by
  apply AlternatingMap.map_linearDependent
  intro hli
  have h := (linearIndependent_iff_card_le_finrank_span).mp hli
  simp only [Fintype.card_fin,Set.finrank] at h
  omega

theorem copyPermutation_productVector (D k : ℕ) (σ : Equiv.Perm (Fin k))
    (z : Fin k → Fin D → ℂ) :
    copyPermutationMatrix D k σ⁻¹ *ᵥ productVector D k z =
      productVector D k (z ∘ σ) := by
  rw [copyPermutationMatrix,Matrix.permMatrix_mulVec]
  ext w
  change (∏ i, z i (w (σ.symm i))) = ∏ i, z (σ i) (w i)
  have h := Equiv.prod_comp σ (fun i => z i (w (σ.symm i)))
  simpa only [Equiv.symm_apply_apply] using h.symm

/-- An actual unnormalized antisymmetrizer built from actual copy permutations. -/
def tensorAntisymmetrizer (D k : ℕ) : Matrix (Word D k) (Word D k) ℂ :=
  ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : ℤ) • copyPermutationMatrix D k σ⁻¹

theorem tensorAntisymmetrizer_productVector (D k : ℕ) (z : Fin k → Fin D → ℂ) :
    tensorAntisymmetrizer D k *ᵥ productVector D k z = alternatingTensorMap D k z := by
  simp only [tensorAntisymmetrizer,Matrix.sum_mulVec,Matrix.smul_mulVec,
    alternatingTensorMap,MultilinearMap.alternatization_apply,copyPermutation_productVector,
    MultilinearMap.domDomCongr_apply,productTensorMultilinear_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rfl

/-- The actual rank-budget support obeys the full-column alternating cutoff.
This is one necessary Young-column annihilation theorem, not a classification. -/
theorem tensorAntisymmetrizer_annihilates_rankBudgetSpace (D k s : ℕ) (hsk : s < k)
    (v : Word D k → ℂ) (hv : v ∈ rankBudgetSpace D k s) :
    tensorAntisymmetrizer D k *ᵥ v = 0 := by
  have hle : rankBudgetSpace D k s ≤ LinearMap.ker (tensorAntisymmetrizer D k).mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z,hz,rfl⟩
    change tensorAntisymmetrizer D k *ᵥ productVector D k z = 0
    rw [tensorAntisymmetrizer_productVector]
    exact alternatingTensorMap_rank_deficient D k s hsk z hz
  exact hle hv

theorem tensorAntisymmetrizer_mul_rankBudgetProjector (D k s : ℕ) (hsk : s < k) :
    tensorAntisymmetrizer D k * rankBudgetProjector D k s = 0 := by
  ext v w
  have hw : (rankBudgetProjector D k s).col w ∈ rankBudgetSpace D k s := by
    rw [← rankBudgetProjector_range,Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨w,rfl⟩
  have h := congrFun (tensorAntisymmetrizer_annihilates_rankBudgetSpace D k s hsk _ hw) v
  simpa only [Matrix.mulVec,dotProduct,Matrix.mul_apply,Matrix.col,Matrix.transpose_apply,
    Pi.zero_apply,Matrix.zero_apply] using h

end
end ExtractionSchur
