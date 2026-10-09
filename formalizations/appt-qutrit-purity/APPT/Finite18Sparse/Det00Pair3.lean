import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det00Pair3 : SparsePolynomial.Poly := [([1,15], -2), ([1,16], -2), ([1,17], -2), ([2,15], -2), ([2,16], -2), ([2,17], -2), ([3,15], -2), ([3,16], -2), ([3,17], -2), ([4,15], -2), ([4,16], -2), ([4,17], -2), ([5,15], -2), ([5,16], -2), ([5,17], -2), ([6,15], -2), ([6,16], -2), ([6,17], -2), ([7,15], -2), ([7,16], -2), ([7,17], -2), ([8,15], -2), ([8,16], -2), ([8,17], -2), ([9,15], -2), ([9,16], -2), ([9,17], -2), ([10,15], -2), ([10,16], -2), ([10,17], -2), ([11,15], -2), ([11,16], -2), ([11,17], -2), ([12,15], -2), ([12,16], -2), ([12,17], -2), ([13,15], -2), ([13,16], -2), ([13,17], -2)]
theorem det00Pair3_data : det00Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryA11 entryA20) := by decide +kernel
theorem eval_det00Pair3 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair3 = matA (outer g) 1 1 * matA (outer g) 2 0 := by
  rw [det00Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA11, eval_entryA20]

end APPT.Finite18
