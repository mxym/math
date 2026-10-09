import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Pair0 : SparsePolynomial.Poly := [([3,5], 4), ([3,6], 4), ([3,7], 4), ([3,8], 4), ([4,5], 4), ([4,6], 4), ([4,7], 4), ([4,8], 4), ([5,5], 4), ([5,6], 8), ([5,7], 8), ([5,8], 8), ([6,6], 4), ([6,7], 8), ([6,8], 8), ([7,7], 4), ([7,8], 8), ([8,8], 4)]
theorem det03Pair0_data : det03Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB22) := by decide +kernel
theorem eval_det03Pair0 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det03Pair0 = matB (outer g) 1 1 * matB (outer g) 2 2 := by
  rw [det03Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB22]

end APPT.Finite9
