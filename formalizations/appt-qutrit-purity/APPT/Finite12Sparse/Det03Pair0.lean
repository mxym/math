import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Pair0 : SparsePolynomial.Poly := [([6,8], 4), ([6,9], 4), ([6,10], 4), ([6,11], 4), ([7,8], 4), ([7,9], 4), ([7,10], 4), ([7,11], 4), ([8,8], 4), ([8,9], 8), ([8,10], 8), ([8,11], 8), ([9,9], 4), ([9,10], 8), ([9,11], 8), ([10,10], 4), ([10,11], 8), ([11,11], 4)]
theorem det03Pair0_data : det03Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB22) := by decide +kernel
theorem eval_det03Pair0 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) det03Pair0 = matB (outer g) 1 1 * matB (outer g) 2 2 := by
  rw [det03Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB22]

end APPT.Finite12
