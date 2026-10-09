import APPT.Finite24Sparse.Join033
import APPT.Finite24Sparse.Target
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

theorem target_coefficients : join033 = SparsePolynomial.scale (5315587200 : Int) targetCoeffs := by decide +kernel
theorem certificate_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ (32*(total g)^2-676*squareTotal g)*total g := by
  have h := join033_nonneg g hg hA hB
  rw [target_coefficients, SparsePolynomial.eval_scale, eval_targetCoeffs] at h
  have hq : (0 : ℝ) < (5315587200 : Int) := by norm_num
  exact (mul_nonneg_iff_of_pos_left hq).mp h
theorem normalized_bound (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (hT : total g = 1) :
    squareTotal g ≤ (32 : ℝ)/676 := by
  have h := certificate_nonneg g hg hA hB
  rw [hT] at h
  nlinarith

end APPT.Finite24
