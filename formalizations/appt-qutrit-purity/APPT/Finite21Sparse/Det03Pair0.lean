import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det03Pair0 : SparsePolynomial.Poly := [([15,17], 4), ([15,18], 4), ([15,19], 4), ([15,20], 4), ([16,17], 4), ([16,18], 4), ([16,19], 4), ([16,20], 4), ([17,17], 4), ([17,18], 8), ([17,19], 8), ([17,20], 8), ([18,18], 4), ([18,19], 8), ([18,20], 8), ([19,19], 4), ([19,20], 8), ([20,20], 4)]
theorem det03Pair0_data : det03Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB22) := by decide +kernel
theorem eval_det03Pair0 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) det03Pair0 = matB (outer g) 1 1 * matB (outer g) 2 2 := by
  rw [det03Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB22]

end APPT.Finite21
