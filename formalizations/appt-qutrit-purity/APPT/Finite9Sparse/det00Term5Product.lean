import APPT.Finite9Sparse.det00Term5Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Term5Coeffs : CoefficientMerge.Poly := [(188, 2), (197, 4), (278, 2)]
theorem det00Term5Coeffs_data : det00Term5Coeffs = CoefficientMerge.trim det00Term5Row00 := by decide +kernel
theorem eval_det00Term5Coeffs (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term5Coeffs = SparsePolynomial.eval (gapValues g) entryA00 * SparsePolynomial.eval (gapValues g) det00Pair5 := by
  rw [det00Term5Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det00Term5Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det00Pair5 = v
  simp only [entryA00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite9
