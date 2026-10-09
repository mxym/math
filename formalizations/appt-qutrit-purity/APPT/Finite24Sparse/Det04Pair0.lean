import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Pair0 : SparsePolynomial.Poly := [([18,20], 4), ([18,21], 4), ([18,22], 4), ([18,23], 4), ([19,20], 4), ([19,21], 4), ([19,22], 4), ([19,23], 4), ([20,20], 4), ([20,21], 8), ([20,22], 8), ([20,23], 8), ([21,21], 4), ([21,22], 8), ([21,23], 8), ([22,22], 4), ([22,23], 8), ([23,23], 4)]
theorem det04Pair0_data : det04Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB22) := by decide +kernel
theorem eval_det04Pair0 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair0 = matB (outer g) 1 1 * matB (outer g) 2 2 := by
  rw [det04Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB22]

end APPT.Finite24
