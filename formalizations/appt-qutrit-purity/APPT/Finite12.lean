import APPT.Finite12Sparse.Join003
import APPT.Finite12Sparse.Target
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

theorem target_coefficients : join003 = SparsePolynomial.scale (24 : Int) targetCoeffs := by decide +kernel
theorem certificate_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ (20*(total g)^2-196*squareTotal g)*total g := by
  have h := join003_nonneg g hg hA hB
  rw [target_coefficients, SparsePolynomial.eval_scale, eval_targetCoeffs] at h
  have hq : (0 : ℝ) < (24 : Int) := by norm_num
  exact (mul_nonneg_iff_of_pos_left hq).mp h
theorem normalized_bound (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) (hT : total g = 1) :
    squareTotal g ≤ (20 : ℝ)/196 := by
  have h := certificate_nonneg g hg hA hB
  rw [hT] at h
  nlinarith

end APPT.Finite12
