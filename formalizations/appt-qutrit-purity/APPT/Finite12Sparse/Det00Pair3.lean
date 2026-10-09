import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Pair3 : SparsePolynomial.Poly := [([1,9], -2), ([1,10], -2), ([1,11], -2), ([2,9], -2), ([2,10], -2), ([2,11], -2), ([3,9], -2), ([3,10], -2), ([3,11], -2), ([4,9], -2), ([4,10], -2), ([4,11], -2), ([5,9], -2), ([5,10], -2), ([5,11], -2), ([6,9], -2), ([6,10], -2), ([6,11], -2), ([7,9], -2), ([7,10], -2), ([7,11], -2)]
theorem det00Pair3_data : det00Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryA11 entryA20) := by decide +kernel
theorem eval_det00Pair3 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair3 = matA (outer g) 1 1 * matA (outer g) 2 0 := by
  rw [det00Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA11, eval_entryA20]

end APPT.Finite12
