import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def base08 : SparsePolynomial.Poly := [([0], -8), ([1], -12), ([2], -16), ([3], -16), ([4], -16), ([5], -16), ([6], -16), ([7], -16), ([8], -16), ([9], -16), ([10], -16), ([11], -16), ([12], -16), ([13], -16), ([14], -16), ([15], -16), ([16], -16), ([17], -16), ([18], -14), ([19], -10), ([20], -2), ([21], 2), ([22], 10), ([23], 18)]
theorem eval_base08 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) base08 = quadB (outer g) ![2,2,1] := by
  norm_num [base08, SparsePolynomial.eval, SparsePolynomial.mon, variables, spectrum, quadB, matB, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base08_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) base08 := by
  rw [eval_base08]
  exact quadB_nonneg (outer g) hB ![2,2,1]

end APPT.Finite24
