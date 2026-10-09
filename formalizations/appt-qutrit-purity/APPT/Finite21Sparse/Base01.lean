import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def base01 : SparsePolynomial.Poly := [([0], -4), ([1], -12), ([2], -16), ([3], -16), ([4], -16), ([5], -16), ([6], -16), ([7], -16), ([8], -16), ([9], -16), ([10], -16), ([11], -16), ([12], -16), ([13], -16), ([14], -16), ([15], -8), ([16], -4), ([17], 4), ([18], 6), ([19], 10), ([20], 18)]
theorem eval_base01 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) base01 = quadA (outer g) ![2,1,2] := by
  norm_num [base01, SparsePolynomial.eval, SparsePolynomial.mon, variables, spectrum, quadA, matA, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base01_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) base01 := by
  rw [eval_base01]
  exact quadA_nonneg (outer g) hA ![2,1,2]

end APPT.Finite21
