import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def base02 : SparsePolynomial.Poly := [([0], -4), ([1], -12), ([2], -16), ([3], -16), ([4], -16), ([5], -16), ([6], -16), ([7], -16), ([8], -16), ([9], -8), ([10], -4), ([11], 4), ([12], 6), ([13], 10), ([14], 18)]
theorem eval_base02 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) base02 = quadA (outer g) ![2,1,2] := by
  norm_num [base02, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, quadA, matA, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base02_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base02 := by
  rw [eval_base02]
  exact quadA_nonneg (outer g) hA ![2,1,2]

end APPT.Finite15
