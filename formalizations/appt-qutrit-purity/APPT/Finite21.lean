import APPT.Finite21Sparse.Join022
import APPT.Finite21Sparse.Target
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

theorem target_coefficients : join022 = CoefficientMerge.scale (966470400 : Int) targetCoeffs := by decide +kernel
theorem certificate_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ (29*(total g)^2-529*squareTotal g)*total g := by
  have h := join022_nonneg g hg hA hB
  rw [target_coefficients, CoefficientMerge.eval_scale, eval_targetCoeffs] at h
  have hq : (0 : ℝ) < (966470400 : Int) := by norm_num
  exact (mul_nonneg_iff_of_pos_left hq).mp h
theorem normalized_bound (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (hT : total g = 1) :
    squareTotal g ≤ (29 : ℝ)/529 := by
  have h := certificate_nonneg g hg hA hB
  rw [hT] at h
  nlinarith

end APPT.Finite21
