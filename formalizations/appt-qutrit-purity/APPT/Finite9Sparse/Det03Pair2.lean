import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Pair2 : SparsePolynomial.Poly := [([0,2], 1), ([0,3], 1), ([1,2], 1), ([1,3], 1), ([2,2], 1), ([2,3], 2), ([2,4], 1), ([2,5], 1), ([2,6], 1), ([3,3], 1), ([3,4], 1), ([3,5], 1), ([3,6], 1)]
theorem det03Pair2_data : det03Pair2 = SparsePolynomial.trim (SparsePolynomial.mul entryB10 entryB21) := by decide +kernel
theorem eval_det03Pair2 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det03Pair2 = matB (outer g) 1 0 * matB (outer g) 2 1 := by
  rw [det03Pair2_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB10, eval_entryB21]

end APPT.Finite9
