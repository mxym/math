import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Pair2 : SparsePolynomial.Poly := [([0,2], 1), ([0,3], 1), ([0,4], 1), ([0,5], 1), ([0,6], 1), ([1,2], 1), ([1,3], 1), ([1,4], 1), ([1,5], 1), ([1,6], 1), ([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([2,7], 1), ([2,8], 1), ([2,9], 1), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 1), ([3,8], 1), ([3,9], 1), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 1), ([4,8], 1), ([4,9], 1), ([5,5], 1), ([5,6], 2), ([5,7], 1), ([5,8], 1), ([5,9], 1), ([6,6], 1), ([6,7], 1), ([6,8], 1), ([6,9], 1)]
theorem det00Pair2_data : det00Pair2 = SparsePolynomial.trim (SparsePolynomial.mul entryA10 entryA21) := by decide +kernel
theorem eval_det00Pair2 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair2 = matA (outer g) 1 0 * matA (outer g) 2 1 := by
  rw [det00Pair2_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA10, eval_entryA21]

end APPT.Finite12
