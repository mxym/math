import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det00Pair0 : SparsePolynomial.Poly := [([12,15], 4), ([12,16], 4), ([12,17], 4), ([13,15], 4), ([13,16], 4), ([13,17], 4), ([14,15], 4), ([14,16], 4), ([14,17], 4), ([15,15], 4), ([15,16], 8), ([15,17], 8), ([16,16], 4), ([16,17], 8), ([17,17], 4)]
theorem det00Pair0_data : det00Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryA11 entryA22) := by decide +kernel
theorem eval_det00Pair0 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair0 = matA (outer g) 1 1 * matA (outer g) 2 2 := by
  rw [det00Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA11, eval_entryA22]

end APPT.Finite18
