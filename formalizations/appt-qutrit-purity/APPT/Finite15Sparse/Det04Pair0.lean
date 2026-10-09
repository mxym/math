import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Pair0 : SparsePolynomial.Poly := [([9,11], 4), ([9,12], 4), ([9,13], 4), ([9,14], 4), ([10,11], 4), ([10,12], 4), ([10,13], 4), ([10,14], 4), ([11,11], 4), ([11,12], 8), ([11,13], 8), ([11,14], 8), ([12,12], 4), ([12,13], 8), ([12,14], 8), ([13,13], 4), ([13,14], 8), ([14,14], 4)]
theorem det04Pair0_data : det04Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB22) := by decide +kernel
theorem eval_det04Pair0 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair0 = matB (outer g) 1 1 * matB (outer g) 2 2 := by
  rw [det04Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB22]

end APPT.Finite15
