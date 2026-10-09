import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Pair0 : SparsePolynomial.Poly := [([6,9], 4), ([6,10], 4), ([6,11], 4), ([7,9], 4), ([7,10], 4), ([7,11], 4), ([8,9], 4), ([8,10], 4), ([8,11], 4), ([9,9], 4), ([9,10], 8), ([9,11], 8), ([10,10], 4), ([10,11], 8), ([11,11], 4)]
theorem det00Pair0_data : det00Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryA11 entryA22) := by decide +kernel
theorem eval_det00Pair0 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair0 = matA (outer g) 1 1 * matA (outer g) 2 2 := by
  rw [det00Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA11, eval_entryA22]

end APPT.Finite12
