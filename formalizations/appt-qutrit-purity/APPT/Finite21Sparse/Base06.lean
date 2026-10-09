import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def base06 : SparsePolynomial.Poly := [([0], -4), ([1], -8), ([2], -16), ([3], -16), ([4], -16), ([5], -16), ([6], -16), ([7], -16), ([8], -16), ([9], -16), ([10], -16), ([11], -16), ([12], -16), ([13], -16), ([14], -16), ([15], -8), ([17], 8), ([18], 12), ([19], 16), ([20], 18)]
theorem eval_base06 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) base06 = quadB (outer g) ![1,2,2] := by
  norm_num [base06, SparsePolynomial.eval, SparsePolynomial.mon, variables, spectrum, quadB, matB, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base06_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) base06 := by
  rw [eval_base06]
  exact quadB_nonneg (outer g) hB ![1,2,2]

end APPT.Finite21
