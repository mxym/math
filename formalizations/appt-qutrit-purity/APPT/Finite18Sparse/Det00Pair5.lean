import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det00Pair5 : SparsePolynomial.Poly := [([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([2,7], 2), ([2,8], 2), ([2,9], 2), ([2,10], 2), ([2,11], 2), ([2,12], 2), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([3,9], 2), ([3,10], 2), ([3,11], 2), ([3,12], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([4,9], 2), ([4,10], 2), ([4,11], 2), ([4,12], 2), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([5,9], 2), ([5,10], 2), ([5,11], 2), ([5,12], 2), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([6,9], 2), ([6,10], 2), ([6,11], 2), ([6,12], 2), ([7,7], 1), ([7,8], 2), ([7,9], 2), ([7,10], 2), ([7,11], 2), ([7,12], 2), ([8,8], 1), ([8,9], 2), ([8,10], 2), ([8,11], 2), ([8,12], 2), ([9,9], 1), ([9,10], 2), ([9,11], 2), ([9,12], 2), ([10,10], 1), ([10,11], 2), ([10,12], 2), ([11,11], 1), ([11,12], 2), ([12,12], 1)]
theorem det00Pair5_data : det00Pair5 = SparsePolynomial.trim (SparsePolynomial.mul entryA12 entryA21) := by decide +kernel
theorem eval_det00Pair5 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair5 = matA (outer g) 1 2 * matA (outer g) 2 1 := by
  rw [det00Pair5_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA12, eval_entryA21]

end APPT.Finite18
