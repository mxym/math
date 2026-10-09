import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Pair4 : SparsePolynomial.Poly := [([0,6], -2), ([0,7], -2), ([0,8], -2), ([0,9], -2), ([0,10], -2), ([0,11], -2), ([1,6], -2), ([1,7], -2), ([1,8], -2), ([1,9], -2), ([1,10], -2), ([1,11], -2), ([2,6], -2), ([2,7], -2), ([2,8], -2), ([2,9], -2), ([2,10], -2), ([2,11], -2), ([3,6], -2), ([3,7], -2), ([3,8], -2), ([3,9], -2), ([3,10], -2), ([3,11], -2), ([4,6], -2), ([4,7], -2), ([4,8], -2), ([4,9], -2), ([4,10], -2), ([4,11], -2), ([5,6], -2), ([5,7], -2), ([5,8], -2), ([5,9], -2), ([5,10], -2), ([5,11], -2), ([6,6], -2), ([6,7], -4), ([6,8], -4), ([6,9], -4), ([6,10], -2), ([6,11], -2), ([7,7], -2), ([7,8], -4), ([7,9], -4), ([7,10], -2), ([7,11], -2), ([8,8], -2), ([8,9], -4), ([8,10], -2), ([8,11], -2), ([9,9], -2), ([9,10], -2), ([9,11], -2)]
theorem det00Pair4_data : det00Pair4 = SparsePolynomial.trim (SparsePolynomial.mul entryA10 entryA22) := by decide +kernel
theorem eval_det00Pair4 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair4 = matA (outer g) 1 0 * matA (outer g) 2 2 := by
  rw [det00Pair4_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA10, eval_entryA22]

end APPT.Finite12
