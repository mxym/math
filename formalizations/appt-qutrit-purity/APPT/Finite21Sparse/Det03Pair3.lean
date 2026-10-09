import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det03Pair3 : SparsePolynomial.Poly := [([1,17], -2), ([1,18], -2), ([1,19], -2), ([1,20], -2), ([2,17], -2), ([2,18], -2), ([2,19], -2), ([2,20], -2), ([3,17], -2), ([3,18], -2), ([3,19], -2), ([3,20], -2), ([4,17], -2), ([4,18], -2), ([4,19], -2), ([4,20], -2), ([5,17], -2), ([5,18], -2), ([5,19], -2), ([5,20], -2), ([6,17], -2), ([6,18], -2), ([6,19], -2), ([6,20], -2), ([7,17], -2), ([7,18], -2), ([7,19], -2), ([7,20], -2), ([8,17], -2), ([8,18], -2), ([8,19], -2), ([8,20], -2), ([9,17], -2), ([9,18], -2), ([9,19], -2), ([9,20], -2), ([10,17], -2), ([10,18], -2), ([10,19], -2), ([10,20], -2), ([11,17], -2), ([11,18], -2), ([11,19], -2), ([11,20], -2), ([12,17], -2), ([12,18], -2), ([12,19], -2), ([12,20], -2), ([13,17], -2), ([13,18], -2), ([13,19], -2), ([13,20], -2), ([14,17], -2), ([14,18], -2), ([14,19], -2), ([14,20], -2), ([15,17], -2), ([15,18], -2), ([15,19], -2), ([15,20], -2), ([16,17], -2), ([16,18], -2), ([16,19], -2), ([16,20], -2), ([17,17], -2), ([17,18], -2), ([17,19], -2), ([17,20], -2)]
theorem det03Pair3_data : det03Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB20) := by decide +kernel
theorem eval_det03Pair3 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) det03Pair3 = matB (outer g) 1 1 * matB (outer g) 2 0 := by
  rw [det03Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB20]

end APPT.Finite21
