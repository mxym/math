import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Pair3 : SparsePolynomial.Poly := [([1,20], -2), ([1,21], -2), ([1,22], -2), ([1,23], -2), ([2,20], -2), ([2,21], -2), ([2,22], -2), ([2,23], -2), ([3,20], -2), ([3,21], -2), ([3,22], -2), ([3,23], -2), ([4,20], -2), ([4,21], -2), ([4,22], -2), ([4,23], -2), ([5,20], -2), ([5,21], -2), ([5,22], -2), ([5,23], -2), ([6,20], -2), ([6,21], -2), ([6,22], -2), ([6,23], -2), ([7,20], -2), ([7,21], -2), ([7,22], -2), ([7,23], -2), ([8,20], -2), ([8,21], -2), ([8,22], -2), ([8,23], -2), ([9,20], -2), ([9,21], -2), ([9,22], -2), ([9,23], -2), ([10,20], -2), ([10,21], -2), ([10,22], -2), ([10,23], -2), ([11,20], -2), ([11,21], -2), ([11,22], -2), ([11,23], -2), ([12,20], -2), ([12,21], -2), ([12,22], -2), ([12,23], -2), ([13,20], -2), ([13,21], -2), ([13,22], -2), ([13,23], -2), ([14,20], -2), ([14,21], -2), ([14,22], -2), ([14,23], -2), ([15,20], -2), ([15,21], -2), ([15,22], -2), ([15,23], -2), ([16,20], -2), ([16,21], -2), ([16,22], -2), ([16,23], -2), ([17,20], -2), ([17,21], -2), ([17,22], -2), ([17,23], -2), ([18,20], -2), ([18,21], -2), ([18,22], -2), ([18,23], -2), ([19,20], -2), ([19,21], -2), ([19,22], -2), ([19,23], -2), ([20,20], -2), ([20,21], -2), ([20,22], -2), ([20,23], -2)]
theorem det04Pair3_data : det04Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB20) := by decide +kernel
theorem eval_det04Pair3 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair3 = matB (outer g) 1 1 * matB (outer g) 2 0 := by
  rw [det04Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB20]

end APPT.Finite24
