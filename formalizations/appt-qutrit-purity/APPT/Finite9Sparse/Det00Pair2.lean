import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Pair2 : SparsePolynomial.Poly := [([0,2], 1), ([0,3], 1), ([1,2], 1), ([1,3], 1), ([2,2], 1), ([2,3], 2), ([2,4], 1), ([2,5], 1), ([2,6], 1), ([3,3], 1), ([3,4], 1), ([3,5], 1), ([3,6], 1)]
theorem det00Pair2_data : det00Pair2 = SparsePolynomial.trim (SparsePolynomial.mul entryA10 entryA21) := by decide +kernel
theorem eval_det00Pair2 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair2 = matA (outer g) 1 0 * matA (outer g) 2 1 := by
  rw [det00Pair2_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA10, eval_entryA21]

end APPT.Finite9
