import SchurCompletion.ExteriorCoordinates
import Mathlib.LinearAlgebra.Trace

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

theorem coordinateWedgeMap_copyPermutation (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    (coordinateWedgeMap D k).comp (copyPermutationMatrix D k σ⁻¹).mulVecLin =
      (Equiv.Perm.sign σ : ℤ) • coordinateWedgeMap D k := by
  apply (Pi.basisFun ℂ (Word D k)).ext
  intro w
  rw [Pi.basisFun_apply]
  change coordinateWedgeMap D k (copyPermutationMatrix D k σ⁻¹ *ᵥ Pi.single w 1) =
    (Equiv.Perm.sign σ : ℤ) • coordinateWedgeMap D k (Pi.single w 1)
  rw [← productVector_basis D k w,copyPermutation_productVector,
    coordinateWedgeMap_productVector,coordinateWedgeMap_productVector]
  simpa only [Units.smul_def] using
    (exteriorPower.ιMulti ℂ k (M := Fin D → ℂ)).map_perm (fun j => Pi.single (w j) 1) σ

theorem tensorAntisymmetrizer_mul_copyPermutation (D k : ℕ) (σ : Equiv.Perm (Fin k)) :
    tensorAntisymmetrizer D k * copyPermutationMatrix D k σ =
      (Equiv.Perm.sign σ : ℤ) • tensorAntisymmetrizer D k := by
  apply Matrix.toLin'.injective
  change (tensorAntisymmetrizer D k * copyPermutationMatrix D k σ).mulVecLin = _
  rw [Matrix.mulVecLin_mul,← exteriorTensorEmbedding_coordinateWedgeMap]
  rw [LinearMap.comp_assoc,← inv_inv σ,coordinateWedgeMap_copyPermutation]
  simp only [Equiv.Perm.sign_inv]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply,LinearMap.smul_apply,map_zsmul,Matrix.toLin'_apply,
    Matrix.smul_mulVec]
  change (Equiv.Perm.sign σ : ℤ) • exteriorTensorEmbedding D k (coordinateWedgeMap D k v) =
    (Equiv.Perm.sign σ : ℤ) • (tensorAntisymmetrizer D k *ᵥ v)
  exact congrArg (fun x => (Equiv.Perm.sign σ : ℤ) • x)
    (DFunLike.congr_fun (exteriorTensorEmbedding_coordinateWedgeMap D k) v)

theorem tensorAntisymmetrizer_hermitian (D k : ℕ) :
    (tensorAntisymmetrizer D k).IsHermitian := by
  change (tensorAntisymmetrizer D k)ᴴ = tensorAntisymmetrizer D k
  simp only [tensorAntisymmetrizer,Matrix.conjTranspose_sum,Matrix.conjTranspose_smul,
    star_trivial,copyPermutationMatrix_star,inv_inv]
  have h := Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin k)))
    (fun σ => (Equiv.Perm.sign σ : ℤ) • copyPermutationMatrix D k σ⁻¹)
  simpa only [Equiv.inv_apply,Equiv.Perm.sign_inv,inv_inv] using h

theorem tensorAntisymmetrizer_square (D k : ℕ) :
    tensorAntisymmetrizer D k * tensorAntisymmetrizer D k =
      (Fintype.card (Equiv.Perm (Fin k)) : ℂ) • tensorAntisymmetrizer D k := by
  apply Matrix.toLin'.injective
  change (tensorAntisymmetrizer D k * tensorAntisymmetrizer D k).mulVecLin = _
  rw [Matrix.mulVecLin_mul,← exteriorTensorEmbedding_coordinateWedgeMap]
  calc
    _ = ((exteriorTensorEmbedding D k).comp
        ((coordinateWedgeMap D k).comp (exteriorTensorEmbedding D k))).comp
          (coordinateWedgeMap D k) := rfl
    _ = _ := by
      rw [coordinateWedgeMap_exteriorTensorEmbedding]
      apply LinearMap.ext
      intro v
      simp only [LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply,map_smul,
        Matrix.mulVecLin_apply,Matrix.smul_mulVec]
      exact congrArg (fun x => (Fintype.card (Equiv.Perm (Fin k)) : ℂ) • x)
        (DFunLike.congr_fun (exteriorTensorEmbedding_coordinateWedgeMap D k) v)

def alternatingProjector (D k : ℕ) : Matrix (Word D k) (Word D k) ℂ :=
  (Fintype.card (Equiv.Perm (Fin k)) : ℂ)⁻¹ • tensorAntisymmetrizer D k

theorem alternatingProjector_hermitian (D k : ℕ) :
    (alternatingProjector D k).IsHermitian := by
  change (alternatingProjector D k)ᴴ = alternatingProjector D k
  simp only [alternatingProjector,Matrix.conjTranspose_smul,star_inv₀,star_natCast,
    (tensorAntisymmetrizer_hermitian D k).eq]

theorem alternatingProjector_idempotent (D k : ℕ) :
    alternatingProjector D k * alternatingProjector D k = alternatingProjector D k := by
  have hn : (Fintype.card (Equiv.Perm (Fin k)) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [alternatingProjector,Matrix.smul_mul,Matrix.mul_smul,
    tensorAntisymmetrizer_square,← mul_smul]
  congr 1
  field_simp

theorem alternatingProjector_rank_choose (D k : ℕ) :
    (alternatingProjector D k).rank = D.choose k := by
  rw [alternatingProjector,Matrix.rank_smul_of_mem_nonZeroDivisors,
    tensorAntisymmetrizer_rank_choose]
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero))

theorem alternatingProjector_trace_choose (D k : ℕ) :
    (alternatingProjector D k).trace = (D.choose k : ℂ) := by
  obtain ⟨κ,iκ,eκ,C,hC,hCP,hcard⟩ := Extraction.exists_projection_factor
    (alternatingProjector D k) (alternatingProjector_hermitian D k)
      (alternatingProjector_idempotent D k)
  letI : Fintype κ := iκ
  letI : DecidableEq κ := eκ
  rw [← hCP,Matrix.trace_mul_comm,hC,Matrix.trace_one,hcard,alternatingProjector_rank_choose]

end
end ExtractionSchur
