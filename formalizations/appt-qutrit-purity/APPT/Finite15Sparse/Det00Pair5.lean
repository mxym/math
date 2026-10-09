import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Pair5 : SparsePolynomial.Poly := [([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([2,7], 2), ([2,8], 2), ([2,9], 2), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([3,9], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([4,9], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([5,9], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([6,9], 2), ([7,7], 1), ([7,8], 2), ([7,9], 2), ([8,8], 1), ([8,9], 2), ([9,9], 1)]
theorem det00Pair5_data : det00Pair5 = SparsePolynomial.trim (SparsePolynomial.mul entryA12 entryA21) := by decide +kernel
theorem eval_det00Pair5 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair5 = matA (outer g) 1 2 * matA (outer g) 2 1 := by
  rw [det00Pair5_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA12, eval_entryA21]

end APPT.Finite15
