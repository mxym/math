import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Pair3 : SparsePolynomial.Poly := [([1,11], -2), ([1,12], -2), ([1,13], -2), ([1,14], -2), ([2,11], -2), ([2,12], -2), ([2,13], -2), ([2,14], -2), ([3,11], -2), ([3,12], -2), ([3,13], -2), ([3,14], -2), ([4,11], -2), ([4,12], -2), ([4,13], -2), ([4,14], -2), ([5,11], -2), ([5,12], -2), ([5,13], -2), ([5,14], -2), ([6,11], -2), ([6,12], -2), ([6,13], -2), ([6,14], -2), ([7,11], -2), ([7,12], -2), ([7,13], -2), ([7,14], -2), ([8,11], -2), ([8,12], -2), ([8,13], -2), ([8,14], -2), ([9,11], -2), ([9,12], -2), ([9,13], -2), ([9,14], -2), ([10,11], -2), ([10,12], -2), ([10,13], -2), ([10,14], -2), ([11,11], -2), ([11,12], -2), ([11,13], -2), ([11,14], -2)]
theorem det04Pair3_data : det04Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB20) := by decide +kernel
theorem eval_det04Pair3 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair3 = matB (outer g) 1 1 * matB (outer g) 2 0 := by
  rw [det04Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB20]

end APPT.Finite15
