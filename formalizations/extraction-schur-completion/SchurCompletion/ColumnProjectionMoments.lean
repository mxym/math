import SchurCompletion.CodimensionOneMoments

open scoped BigOperators ComplexOrder
open Matrix MeasureTheory

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section

theorem coordinateRankProjection_tensor_factor (D s k : ℕ) (hsD : s ≤ D) :
    tensorMatrix (coordinateRankProjection D s hsD) k =
      Extraction.coordinateIsometry (coordinateWordEmbedding k hsD) *
        (Extraction.coordinateIsometry (coordinateWordEmbedding k hsD))ᴴ := by
  rw [coordinateRankProjection, rectangularTensor_mul_conjTranspose,
    rectangularTensor_coordinateIsometry]

theorem symmetricProjector_coordinateIsometry (D s k : ℕ) (hsD : s ≤ D) :
    symmetricProjector D k * Extraction.coordinateIsometry (coordinateWordEmbedding k hsD) =
      Extraction.coordinateIsometry (coordinateWordEmbedding k hsD) * symmetricProjector s k := by
  rw [symmetricProjector_eq_copyPermutationAverage, symmetricProjector_eq_copyPermutationAverage]
  simp only [copyPermutationAverage, Matrix.smul_mul, Matrix.sum_mul, Matrix.mul_smul,
    Matrix.mul_sum, copyPermutation_coordinateIsometry]

theorem coordinateRankProjection_symmetric_moment (D s k : ℕ) (hsD : s ≤ D) :
    (tensorMatrix (coordinateRankProjection D s hsD) k * symmetricProjector D k).trace =
      ((s+k-1).choose k : ℂ) := by
  let C := Extraction.coordinateIsometry (coordinateWordEmbedding k hsD)
  have hC : Cᴴ * C = 1 := Extraction.coordinateIsometry_isometry _
  rw [coordinateRankProjection_tensor_factor, Matrix.trace_mul_comm]
  change (symmetricProjector D k * (C*Cᴴ)).trace = _
  rw [← Matrix.mul_assoc, symmetricProjector_coordinateIsometry, Matrix.trace_mul_cycle]
  change (Cᴴ * C * symmetricProjector s k).trace = _
  rw [hC, Matrix.one_mul, symmetricProjector_trace_choose]

/-- Exact beta moments of the squared projection of a genuine Haar column
onto any coordinate s-subspace. They are derived from the actual rank-one
orbit average, with no distribution or moment certificate as input. -/
theorem unitary_column_projection_power_moment (D s k : ℕ) (hsD : s ≤ D) (a : Fin D) :
    (∫ U : OneCopyUnitary D,
      (coordinateRankProjection D s hsD *
        ((U : Matrix (Fin D) (Fin D) ℂ) * coordinatePureProjection D a *
          (U : Matrix (Fin D) (Fin D) ℂ)ᴴ)).trace ^ k ∂unitaryHaar D) =
      ((s+k-1).choose k : ℂ) / ((D+k-1).choose k : ℂ) := by
  have hD : 0 < D := Nat.zero_lt_of_lt a.isLt
  have h := haarOrbitAverage_traceLeft D k (coordinatePureProjection D a)
    (tensorMatrix (coordinateRankProjection D s hsD) k)
  rw [haarOrbitAverage_rank_one D k hD (coordinatePureProjection D a)
    (coordinatePureProjection_density D a) (coordinatePureProjection_rank D a)] at h
  have he : (tensorMatrix (coordinateRankProjection D s hsD) k * symmetricState D k).trace =
      ((s+k-1).choose k : ℂ) / ((D+k-1).choose k : ℂ) := by
    rw [symmetricState, Matrix.mul_smul, Matrix.trace_smul,
      coordinateRankProjection_symmetric_moment]
    simp [Sym.card_sym_eq_choose, RCLike.real_smul_eq_coe_mul, div_eq_mul_inv, mul_comm]
  rw [he] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with U
  rw [orbitTensor, ← tensorMatrix_mul, actual_tensorMatrix_trace]

end
end ExtractionSchur
