import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Pair3 : SparsePolynomial.Poly := [([1,6], -2), ([1,7], -2), ([1,8], -2), ([2,6], -2), ([2,7], -2), ([2,8], -2), ([3,6], -2), ([3,7], -2), ([3,8], -2), ([4,6], -2), ([4,7], -2), ([4,8], -2)]
theorem det00Pair3_data : det00Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryA11 entryA20) := by decide +kernel
theorem eval_det00Pair3 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair3 = matA (outer g) 1 1 * matA (outer g) 2 0 := by
  rw [det00Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA11, eval_entryA20]

end APPT.Finite9
