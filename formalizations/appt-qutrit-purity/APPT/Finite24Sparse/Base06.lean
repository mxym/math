import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def base06 : SparsePolynomial.Poly := [([0], -2), ([1], -2), ([2], -2), ([3], -2), ([4], -2), ([5], -2), ([6], -2), ([7], -2), ([8], -2), ([9], -2), ([10], -2), ([11], -2), ([12], -2), ([13], -2), ([14], -2), ([15], -2), ([16], -2), ([17], -2), ([18], -2), ([19], -2), ([22], 2), ([23], 4)]
theorem eval_base06 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) base06 = quadB (outer g) ![1,1,0] := by
  norm_num [base06, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, quadB, matB, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base06_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base06 := by
  rw [eval_base06]
  exact quadB_nonneg (outer g) hB ![1,1,0]

end APPT.Finite24
