import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Pair4 : SparsePolynomial.Poly := [([0,9], -2), ([0,10], -2), ([0,11], -2), ([0,12], -2), ([0,13], -2), ([0,14], -2), ([1,9], -2), ([1,10], -2), ([1,11], -2), ([1,12], -2), ([1,13], -2), ([1,14], -2), ([2,9], -2), ([2,10], -2), ([2,11], -2), ([2,12], -2), ([2,13], -2), ([2,14], -2), ([3,9], -2), ([3,10], -2), ([3,11], -2), ([3,12], -2), ([3,13], -2), ([3,14], -2), ([4,9], -2), ([4,10], -2), ([4,11], -2), ([4,12], -2), ([4,13], -2), ([4,14], -2), ([5,9], -2), ([5,10], -2), ([5,11], -2), ([5,12], -2), ([5,13], -2), ([5,14], -2), ([6,9], -2), ([6,10], -2), ([6,11], -2), ([6,12], -2), ([6,13], -2), ([6,14], -2), ([7,9], -2), ([7,10], -2), ([7,11], -2), ([7,12], -2), ([7,13], -2), ([7,14], -2), ([8,9], -2), ([8,10], -2), ([8,11], -2), ([8,12], -2), ([8,13], -2), ([8,14], -2), ([9,9], -2), ([9,10], -4), ([9,11], -4), ([9,12], -4), ([9,13], -2), ([9,14], -2), ([10,10], -2), ([10,11], -4), ([10,12], -4), ([10,13], -2), ([10,14], -2), ([11,11], -2), ([11,12], -4), ([11,13], -2), ([11,14], -2), ([12,12], -2), ([12,13], -2), ([12,14], -2)]
theorem det04Pair4_data : det04Pair4 = SparsePolynomial.trim (SparsePolynomial.mul entryB10 entryB22) := by decide +kernel
theorem eval_det04Pair4 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair4 = matB (outer g) 1 0 * matB (outer g) 2 2 := by
  rw [det04Pair4_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB10, eval_entryB22]

end APPT.Finite15
