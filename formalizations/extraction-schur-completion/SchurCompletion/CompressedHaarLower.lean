import SchurCompletion.CyclicTwirlLower
import SchurCompletion.PermutationMoments

open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix MeasureTheory Filter

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section
set_option backward.isDefEq.respectTransparency false

def compressionLinear {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C : Matrix ι κ ℂ) : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ where
  toFun A := Cᴴ*A*C
  map_add' A B := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

theorem coordinate_compression {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : κ ↪ ι) (A : Matrix ι ι ℂ) :
    compressionLinear (Extraction.coordinateIsometry e) A = A.submatrix e e := by
  ext i j
  simp [compressionLinear, Matrix.mul_apply, Extraction.coordinateIsometry, Matrix.conjTranspose_apply]

def haarTwirlLinear (D k : ℕ) :
    Matrix (Word D k) (Word D k) ℂ →ₗ[ℂ] Matrix (Word D k) (Word D k) ℂ where
  toFun := haarTwirl D k
  map_add' A B := by
    simp only [haarTwirl, tensorConjugate, Matrix.mul_add, Matrix.add_mul]
    exact integral_add (integrable_tensorConjugate D k A) (integrable_tensorConjugate D k B)
  map_smul' c A := by
    simp only [haarTwirl, tensorConjugate, Matrix.mul_smul, Matrix.smul_mul, integral_smul,
      RingHom.id_apply]

theorem coordinate_compression_permutation (D s k : ℕ) (hsD : s ≤ D)
    (A : Matrix (Word D k) (Word D k) ℂ) (hA : A ∈ permutationSpan D k) :
    compressionLinear (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD)) A ∈
      permutationSpan s k := by
  let C := Extraction.coordinateIsometry (coordinateWordEmbedding k hsD)
  have hC : Cᴴ*C=1 := Extraction.coordinateIsometry_isometry _
  induction hA using Submodule.span_induction with
  | mem A hA =>
    obtain ⟨σ,rfl⟩ := hA
    have he : compressionLinear C (copyPermutationMatrix D k σ) = copyPermutationMatrix s k σ := by
      change Cᴴ*copyPermutationMatrix D k σ*C = _
      rw [Matrix.mul_assoc, copyPermutation_coordinateIsometry, ← Matrix.mul_assoc, hC, Matrix.one_mul]
    exact he ▸ Submodule.subset_span ⟨σ,rfl⟩
  | zero => simpa using (permutationSpan s k).zero_mem
  | add A B hA hB ihA ihB => simpa only [map_add] using (permutationSpan s k).add_mem ihA ihB
  | smul c A hA ihA => simpa only [map_smul] using (permutationSpan s k).smul_mem c ihA

theorem coordinate_compression_tensor (D s k : ℕ) (hsD : s ≤ D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    compressionLinear (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD)) (tensorMatrix X k) =
      tensorMatrix (X.submatrix (coordinateLetterEmbedding hsD) (coordinateLetterEmbedding hsD)) k := by
  rw [coordinate_compression]
  rfl

theorem continuous_projectedGram (D s : ℕ) (hsD : s ≤ D) : Continuous (projectedGram D s hsD) := by
  unfold projectedGram
  fun_prop

theorem flatHaarAverage_coordinate_compression (D s k : ℕ) (hsD : s ≤ D) :
    compressionLinear (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD))
      (flatHaarAverage D s k hsD) =
      ((s : ℝ)^k)⁻¹ • (∫ U : OneCopyUnitary D, tensorMatrix (projectedGram D s hsD U) k
        ∂unitaryHaar D) := by
  rw [flatHaarAverage, haarOrbitAverage]
  have hm : compressionLinear (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD))
      (∫ U, orbitTensor D k (flatCoordinateDensity D s hsD) U ∂unitaryHaar D) =
      ∫ U, compressionLinear (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD))
        (orbitTensor D k (flatCoordinateDensity D s hsD) U) ∂unitaryHaar D :=
    ((compressionLinear (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD))).toContinuousLinearMap.integral_comp_comm
      (integrable_orbitTensor D k (flatCoordinateDensity D s hsD))).symm
  rw [hm]
  have he (U : OneCopyUnitary D) :
      compressionLinear (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD))
        (orbitTensor D k (flatCoordinateDensity D s hsD) U) =
        ((s : ℝ)^k)⁻¹ • tensorMatrix (projectedGram D s hsD U) k := by
    rw [orbitTensor, coordinate_compression_tensor]
    simp only [flatCoordinateDensity, normalizedProjection, coordinateRankProjection_rank,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul, Pi.smul_apply, projectedGram,
      tensorMatrix_real_smul, inv_pow]
  simp_rw [he]
  exact integral_smul _ _

theorem flatHaarAverage_coordinate_twirl (D s k : ℕ) (hsD : s ≤ D) :
    compressionLinear (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD))
      (flatHaarAverage D s k hsD) =
      ((s : ℝ)^k)⁻¹ • (∫ U : OneCopyUnitary D, haarOrbitAverage s k (projectedGram D s hsD U)
        ∂unitaryHaar D) := by
  have hfix := haarTwirl_eq_self_of_mem s k _ (coordinate_compression_permutation D s k hsD
    (flatHaarAverage D s k hsD) (haarOrbitAverage_mem_permutationSpan D k _))
  rw [flatHaarAverage_coordinate_compression] at hfix
  rw [flatHaarAverage_coordinate_compression, ← hfix, haarTwirl_real_smul]
  congr 1
  have hint : Integrable (fun U : OneCopyUnitary D => tensorMatrix (projectedGram D s hsD U) k)
      (unitaryHaar D) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold tensorMatrix projectedGram
    fun_prop
  change haarTwirlLinear s k (∫ U : OneCopyUnitary D, tensorMatrix (projectedGram D s hsD U) k
    ∂unitaryHaar D) = _
  calc
    _ = ∫ U : OneCopyUnitary D, haarTwirlLinear s k (tensorMatrix (projectedGram D s hsD U) k)
        ∂unitaryHaar D := ((haarTwirlLinear s k).toContinuousLinearMap.integral_comp_comm hint).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with U
      exact (haarOrbitAverage_eq_haarTwirl s k (projectedGram D s hsD U)).symm


/-- The actual Haar average restricted to the canonical rank-s tensor
subspace has a scalar lower bound from an actual principal-minor moment. -/
theorem flatHaarAverage_compressed_lower (D s k q : ℕ) (hs : 0 < s) (hsD : s ≤ D) (hk : k ≤ s*q) :
    (compressionLinear (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD))
      (flatHaarAverage D s k hsD) -
      (((s : ℝ)^k)⁻¹ * (haarMinorMoment D s q hsD).re) •
        (1 : Matrix (Word s k) (Word s k) ℂ)).PosSemidef := by
  have hint : Integrable (fun U : OneCopyUnitary D =>
      haarOrbitAverage s k (projectedGram D s hsD U)) (unitaryHaar D) := by
    simp_rw [haarOrbitAverage_eq_haarTwirl]
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    apply (haarTwirlLinear s k).continuous_of_finiteDimensional.comp
    unfold tensorMatrix projectedGram
    fun_prop
  have hZ : Integrable (fun U : OneCopyUnitary D =>
      Complex.normSq (principalMinor D s hsD U).det^q) (unitaryHaar D) := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    unfold principalMinor
    fun_prop
  have hpoint (U : OneCopyUnitary D) :
      (Complex.normSq (principalMinor D s hsD U).det^q) • (1 : Matrix (Word s k) (Word s k) ℂ) ≤
        haarOrbitAverage s k (projectedGram D s hsD U) := by
    have hG := projectedGram_contraction D s hsD U
    have h := haarOrbitAverage_contraction_lower s k q hs hk _ hG.1 hG.2
    rw [projectedGram_det] at h
    exact sub_nonneg.mp h.nonneg
  have h := integral_mono (hZ.smul_const (1 : Matrix (Word s k) (Word s k) ℂ)) hint hpoint
  rw [integral_smul_const, ← haarMinorMoment_re_integral] at h
  have hh := smul_le_smul_of_nonneg_left h (by positivity : 0 ≤ ((s : ℝ)^k)⁻¹)
  rw [smul_smul, ← flatHaarAverage_coordinate_twirl] at hh
  exact (sub_nonneg.mpr hh).posSemidef

end
end ExtractionSchur
