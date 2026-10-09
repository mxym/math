import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def base08 : SparsePolynomial.Poly := [([0], -8), ([1], -12), ([2], -16), ([3], -16), ([4], -16), ([5], -16), ([6], -16), ([7], -16), ([8], -16), ([9], -16), ([10], -16), ([11], -16), ([12], -14), ([13], -10), ([14], -2), ([15], 2), ([16], 10), ([17], 18)]
theorem eval_base08 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) base08 = quadB (outer g) ![2,2,1] := by
  norm_num [base08, SparsePolynomial.eval, SparsePolynomial.mon, variables, spectrum, quadB, matB, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base08_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) base08 := by
  rw [eval_base08]
  exact quadB_nonneg (outer g) hB ![2,2,1]

end APPT.Finite18
