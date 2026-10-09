import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Pair3 : SparsePolynomial.Poly := [([1,12], -2), ([1,13], -2), ([1,14], -2), ([2,12], -2), ([2,13], -2), ([2,14], -2), ([3,12], -2), ([3,13], -2), ([3,14], -2), ([4,12], -2), ([4,13], -2), ([4,14], -2), ([5,12], -2), ([5,13], -2), ([5,14], -2), ([6,12], -2), ([6,13], -2), ([6,14], -2), ([7,12], -2), ([7,13], -2), ([7,14], -2), ([8,12], -2), ([8,13], -2), ([8,14], -2), ([9,12], -2), ([9,13], -2), ([9,14], -2), ([10,12], -2), ([10,13], -2), ([10,14], -2)]
theorem det00Pair3_data : det00Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryA11 entryA20) := by decide +kernel
theorem eval_det00Pair3 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair3 = matA (outer g) 1 1 * matA (outer g) 2 0 := by
  rw [det00Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA11, eval_entryA20]

end APPT.Finite15
