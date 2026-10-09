import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def base07 : SparsePolynomial.Poly := [([0], -4), ([1], -8), ([2], -16), ([3], -16), ([4], -16), ([5], -16), ([6], -16), ([7], -16), ([8], -16), ([9], -8), ([11], 8), ([12], 12), ([13], 16), ([14], 18)]
theorem eval_base07 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) base07 = quadB (outer g) ![1,2,2] := by
  norm_num [base07, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, quadB, matB, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base07_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base07 := by
  rw [eval_base07]
  exact quadB_nonneg (outer g) hB ![1,2,2]

end APPT.Finite15
