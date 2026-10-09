import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Pair3 : SparsePolynomial.Poly := [([1,5], -2), ([1,6], -2), ([1,7], -2), ([1,8], -2), ([2,5], -2), ([2,6], -2), ([2,7], -2), ([2,8], -2), ([3,5], -2), ([3,6], -2), ([3,7], -2), ([3,8], -2), ([4,5], -2), ([4,6], -2), ([4,7], -2), ([4,8], -2), ([5,5], -2), ([5,6], -2), ([5,7], -2), ([5,8], -2)]
theorem det03Pair3_data : det03Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB20) := by decide +kernel
theorem eval_det03Pair3 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det03Pair3 = matB (outer g) 1 1 * matB (outer g) 2 0 := by
  rw [det03Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB20]

end APPT.Finite9
