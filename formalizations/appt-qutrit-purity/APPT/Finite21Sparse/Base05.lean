import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def base05 : SparsePolynomial.Poly := [([0], -2), ([1], -2), ([2], -2), ([3], -2), ([4], -2), ([5], -2), ([6], -2), ([7], -2), ([8], -2), ([9], -2), ([10], -2), ([11], -2), ([12], -2), ([13], -2), ([14], -2), ([15], -2), ([16], -2), ([19], 2), ([20], 4)]
theorem eval_base05 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) base05 = quadB (outer g) ![1,1,0] := by
  norm_num [base05, SparsePolynomial.eval, SparsePolynomial.mon, variables, spectrum, quadB, matB, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base05_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) base05 := by
  rw [eval_base05]
  exact quadB_nonneg (outer g) hB ![1,1,0]

end APPT.Finite21
