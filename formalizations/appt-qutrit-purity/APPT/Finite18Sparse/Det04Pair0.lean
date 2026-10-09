import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det04Pair0 : SparsePolynomial.Poly := [([12,14], 4), ([12,15], 4), ([12,16], 4), ([12,17], 4), ([13,14], 4), ([13,15], 4), ([13,16], 4), ([13,17], 4), ([14,14], 4), ([14,15], 8), ([14,16], 8), ([14,17], 8), ([15,15], 4), ([15,16], 8), ([15,17], 8), ([16,16], 4), ([16,17], 8), ([17,17], 4)]
theorem det04Pair0_data : det04Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB22) := by decide +kernel
theorem eval_det04Pair0 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair0 = matB (outer g) 1 1 * matB (outer g) 2 2 := by
  rw [det04Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB22]

end APPT.Finite18
