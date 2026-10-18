import SchurCompletion.CompressedHaarLower

open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem compression_low_eigenvector_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℂ) (C : Matrix ι κ ℂ)
    (hC : Cᴴ*C=1) (hcomm : A*(C*Cᴴ)=(C*Cᴴ)*A) (L a : ℝ)
    (hlower : (compressionLinear C A-L • (1 : Matrix κ κ ℂ)).PosSemidef)
    (v : ι → ℂ) (hv : A*ᵥv=a • v) (ha : a < L) : Cᴴ*ᵥv=0 := by
  let x := Cᴴ*ᵥv
  have he : compressionLinear C A * Cᴴ = Cᴴ*A := by
    calc
      _ = Cᴴ*(A*(C*Cᴴ)) := by
        change Cᴴ*A*C*Cᴴ = _
        simp only [Matrix.mul_assoc]
      _ = Cᴴ*((C*Cᴴ)*A) := by rw [hcomm]
      _ = _ := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hC, Matrix.one_mul]
  have hx : compressionLinear C A *ᵥx = a • x := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have hform := hlower.re_dotProduct_nonneg x
  have hnorm := RCLike.nonneg_iff.mp (dotProduct_star_self_nonneg x)
  have hH : (compressionLinear C A-L • (1 : Matrix κ κ ℂ))*ᵥx = (a-L) • x := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hx, sub_smul]
  rw [hH, dotProduct_smul, RCLike.smul_re] at hform
  have hn : RCLike.re (star x ⬝ᵥ x) = 0 := by nlinarith [hnorm.1]
  have hz : star x ⬝ᵥ x = 0 := by
    apply Complex.ext
    · exact hn
    · exact hnorm.2
  exact dotProduct_star_self_eq_zero.mp hz

def applyVectorLinear {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] (ι → ℂ) where
  toFun A := A*ᵥv
  map_add' A B := Matrix.add_mulVec A B v
  map_smul' c A := by simp only [Matrix.smul_mulVec, RingHom.id_apply]

theorem flatHaarAverage_positive_eigenvalue_lower (D s k q : ℕ) (hs : 0 < s) (hsD : s ≤ D)
    (hk : k ≤ s*q) (a : ℝ) (ha : 0 < a) (v : Word D k → ℂ) (hv0 : v ≠ 0)
    (hv : flatHaarAverage D s k hsD *ᵥv=a • v) :
    ((s : ℝ)^k)⁻¹*(haarMinorMoment D s q hsD).re ≤ a := by
  by_contra hnot
  have halt : a < ((s : ℝ)^k)⁻¹*(haarMinorMoment D s q hsD).re := lt_of_not_ge hnot
  let C := Extraction.coordinateIsometry (coordinateWordEmbedding k hsD)
  let Ω := flatHaarAverage D s k hsD
  have hC : Cᴴ*C=1 := Extraction.coordinateIsometry_isometry _
  have hcomm : Ω*(C*Cᴴ)=(C*Cᴴ)*Ω := by
    rw [← coordinateRankProjection_tensor_factor]
    exact haarOrbitAverage_central D k _ _ (Submodule.subset_span ⟨coordinateRankProjection D s hsD,rfl⟩)
  have hlow := flatHaarAverage_compressed_lower D s k q hs hsD hk
  have hz (U : OneCopyUnitary D) :
      Cᴴ*ᵥ((tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ*ᵥv)=0 := by
    have hU : Ω*(tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ =
        (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ*Ω := by
      simpa only [Ω, flatHaarAverage, Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose,
        tensorMatrix_conjTranspose] using (haarOrbitAverage_commutes D k
          (flatCoordinateDensity D s hsD) U⁻¹).symm
    apply compression_low_eigenvector_zero Ω C hC hcomm _ a hlow _ _ halt
    rw [Matrix.mulVec_mulVec, hU, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]
  have horbit (U : OneCopyUnitary D) : orbitTensor D k (flatCoordinateDensity D s hsD) U *ᵥv=0 := by
    rw [orbitTensor, tensorMatrix_mul, tensorMatrix_mul, tensorMatrix_conjTranspose,
      flatCoordinateDensity_tensor_factor, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec]
    change ((s : ℝ)^k)⁻¹ •
      ((tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k * (C*Cᴴ) *
        (tensorMatrix (U : Matrix (Fin D) (Fin D) ℂ) k)ᴴ)*ᵥv)=0
    simp only [← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero, smul_zero]
  have hzΩ : Ω*ᵥv=0 := by
    calc
      _ = ∫ U : OneCopyUnitary D, orbitTensor D k (flatCoordinateDensity D s hsD) U *ᵥv
          ∂unitaryHaar D := ((applyVectorLinear v).toContinuousLinearMap.integral_comp_comm
            (integrable_orbitTensor D k (flatCoordinateDensity D s hsD))).symm
      _ = 0 := by simp only [horbit, integral_zero]
  rw [hv] at hzΩ
  exact hv0 ((smul_eq_zero.mp hzΩ).resolve_left ha.ne')

end
end ExtractionSchur
