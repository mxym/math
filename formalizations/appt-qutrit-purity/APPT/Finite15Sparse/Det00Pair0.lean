import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Pair0 : SparsePolynomial.Poly := [([9,12], 4), ([9,13], 4), ([9,14], 4), ([10,12], 4), ([10,13], 4), ([10,14], 4), ([11,12], 4), ([11,13], 4), ([11,14], 4), ([12,12], 4), ([12,13], 8), ([12,14], 8), ([13,13], 4), ([13,14], 8), ([14,14], 4)]
theorem det00Pair0_data : det00Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryA11 entryA22) := by decide +kernel
theorem eval_det00Pair0 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair0 = matA (outer g) 1 1 * matA (outer g) 2 2 := by
  rw [det00Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA11, eval_entryA22]

end APPT.Finite15
