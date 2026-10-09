import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Pair4 : SparsePolynomial.Poly := [([0,3], -2), ([0,4], -2), ([0,5], -2), ([0,6], -2), ([0,7], -2), ([0,8], -2), ([1,3], -2), ([1,4], -2), ([1,5], -2), ([1,6], -2), ([1,7], -2), ([1,8], -2), ([2,3], -2), ([2,4], -2), ([2,5], -2), ([2,6], -2), ([2,7], -2), ([2,8], -2), ([3,3], -2), ([3,4], -4), ([3,5], -4), ([3,6], -4), ([3,7], -2), ([3,8], -2), ([4,4], -2), ([4,5], -4), ([4,6], -4), ([4,7], -2), ([4,8], -2), ([5,5], -2), ([5,6], -4), ([5,7], -2), ([5,8], -2), ([6,6], -2), ([6,7], -2), ([6,8], -2)]
theorem det03Pair4_data : det03Pair4 = SparsePolynomial.trim (SparsePolynomial.mul entryB10 entryB22) := by decide +kernel
theorem eval_det03Pair4 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det03Pair4 = matB (outer g) 1 0 * matB (outer g) 2 2 := by
  rw [det03Pair4_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB10, eval_entryB22]

end APPT.Finite9
