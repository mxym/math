import APPT.Finite18Sparse.Join014
import APPT.Finite18Sparse.Target
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

theorem target_coefficients : join014 = CoefficientMerge.scale (322560 : Int) targetCoeffs := by decide +kernel
theorem certificate_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ (26*(total g)^2-400*squareTotal g)*total g := by
  have h := join014_nonneg g hg hA hB
  rw [target_coefficients, CoefficientMerge.eval_scale, eval_targetCoeffs] at h
  have hq : (0 : ℝ) < (322560 : Int) := by norm_num
  exact (mul_nonneg_iff_of_pos_left hq).mp h
theorem normalized_bound (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (hT : total g = 1) :
    squareTotal g ≤ (26 : ℝ)/400 := by
  have h := certificate_nonneg g hg hA hB
  rw [hT] at h
  nlinarith

end APPT.Finite18
