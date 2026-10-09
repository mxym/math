import APPT.Finite15Sparse.Join007
import APPT.Finite15Sparse.Target
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

theorem target_coefficients : join007 = CoefficientMerge.scale (8640 : Int) targetCoeffs := by decide +kernel
theorem certificate_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ (23*(total g)^2-289*squareTotal g)*total g := by
  have h := join007_nonneg g hg hA hB
  rw [target_coefficients, CoefficientMerge.eval_scale, eval_targetCoeffs] at h
  have hq : (0 : ℝ) < (8640 : Int) := by norm_num
  exact (mul_nonneg_iff_of_pos_left hq).mp h
theorem normalized_bound (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (hT : total g = 1) :
    squareTotal g ≤ (23 : ℝ)/289 := by
  have h := certificate_nonneg g hg hA hB
  rw [hT] at h
  nlinarith

end APPT.Finite15
