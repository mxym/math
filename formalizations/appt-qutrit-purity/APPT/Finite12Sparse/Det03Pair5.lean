import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Pair5 : SparsePolynomial.Poly := [([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([5,5], 1), ([5,6], 2), ([6,6], 1)]
theorem det03Pair5_data : det03Pair5 = SparsePolynomial.trim (SparsePolynomial.mul entryB12 entryB21) := by decide +kernel
theorem eval_det03Pair5 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) det03Pair5 = matB (outer g) 1 2 * matB (outer g) 2 1 := by
  rw [det03Pair5_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB12, eval_entryB21]

end APPT.Finite12
