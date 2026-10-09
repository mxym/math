import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Pair2 : SparsePolynomial.Poly := [([0,2], 1), ([0,3], 1), ([0,4], 1), ([0,5], 1), ([0,6], 1), ([0,7], 1), ([0,8], 1), ([0,9], 1), ([1,2], 1), ([1,3], 1), ([1,4], 1), ([1,5], 1), ([1,6], 1), ([1,7], 1), ([1,8], 1), ([1,9], 1), ([2,2], 1), ([2,3], 2), ([2,4], 2), ([2,5], 2), ([2,6], 2), ([2,7], 2), ([2,8], 2), ([2,9], 2), ([2,10], 1), ([2,11], 1), ([2,12], 1), ([3,3], 1), ([3,4], 2), ([3,5], 2), ([3,6], 2), ([3,7], 2), ([3,8], 2), ([3,9], 2), ([3,10], 1), ([3,11], 1), ([3,12], 1), ([4,4], 1), ([4,5], 2), ([4,6], 2), ([4,7], 2), ([4,8], 2), ([4,9], 2), ([4,10], 1), ([4,11], 1), ([4,12], 1), ([5,5], 1), ([5,6], 2), ([5,7], 2), ([5,8], 2), ([5,9], 2), ([5,10], 1), ([5,11], 1), ([5,12], 1), ([6,6], 1), ([6,7], 2), ([6,8], 2), ([6,9], 2), ([6,10], 1), ([6,11], 1), ([6,12], 1), ([7,7], 1), ([7,8], 2), ([7,9], 2), ([7,10], 1), ([7,11], 1), ([7,12], 1), ([8,8], 1), ([8,9], 2), ([8,10], 1), ([8,11], 1), ([8,12], 1), ([9,9], 1), ([9,10], 1), ([9,11], 1), ([9,12], 1)]
theorem det04Pair2_data : det04Pair2 = SparsePolynomial.trim (SparsePolynomial.mul entryB10 entryB21) := by decide +kernel
theorem eval_det04Pair2 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair2 = matB (outer g) 1 0 * matB (outer g) 2 1 := by
  rw [det04Pair2_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB10, eval_entryB21]

end APPT.Finite15
