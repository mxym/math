import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det04Pair3 : SparsePolynomial.Poly := [([1,14], -2), ([1,15], -2), ([1,16], -2), ([1,17], -2), ([2,14], -2), ([2,15], -2), ([2,16], -2), ([2,17], -2), ([3,14], -2), ([3,15], -2), ([3,16], -2), ([3,17], -2), ([4,14], -2), ([4,15], -2), ([4,16], -2), ([4,17], -2), ([5,14], -2), ([5,15], -2), ([5,16], -2), ([5,17], -2), ([6,14], -2), ([6,15], -2), ([6,16], -2), ([6,17], -2), ([7,14], -2), ([7,15], -2), ([7,16], -2), ([7,17], -2), ([8,14], -2), ([8,15], -2), ([8,16], -2), ([8,17], -2), ([9,14], -2), ([9,15], -2), ([9,16], -2), ([9,17], -2), ([10,14], -2), ([10,15], -2), ([10,16], -2), ([10,17], -2), ([11,14], -2), ([11,15], -2), ([11,16], -2), ([11,17], -2), ([12,14], -2), ([12,15], -2), ([12,16], -2), ([12,17], -2), ([13,14], -2), ([13,15], -2), ([13,16], -2), ([13,17], -2), ([14,14], -2), ([14,15], -2), ([14,16], -2), ([14,17], -2)]
theorem det04Pair3_data : det04Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB20) := by decide +kernel
theorem eval_det04Pair3 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair3 = matB (outer g) 1 1 * matB (outer g) 2 0 := by
  rw [det04Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB20]

end APPT.Finite18
