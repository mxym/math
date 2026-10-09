import APPT.Finite9Sparse.det03Term5Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term5Coeffs : CoefficientMerge.Poly := [(188, 2), (197, 4), (278, 2)]
theorem det03Term5Coeffs_data : det03Term5Coeffs = CoefficientMerge.trim det03Term5Row00 := by decide +kernel
theorem eval_det03Term5Coeffs (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term5Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det03Pair5 := by
  rw [det03Term5Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term5Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair5 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite9
