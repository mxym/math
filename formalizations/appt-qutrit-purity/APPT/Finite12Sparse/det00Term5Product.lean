import APPT.Finite12Sparse.det00Term5Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term5Coeffs : CoefficientMerge.Poly := [(323, 2), (335, 4), (347, 4), (359, 4), (371, 4), (479, 2), (491, 4), (503, 4), (515, 4), (635, 2), (647, 4), (659, 4), (791, 2), (803, 4), (947, 2)]
theorem det00Term5Coeffs_data : det00Term5Coeffs = CoefficientMerge.trim det00Term5Row00 := by decide +kernel
theorem eval_det00Term5Coeffs (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term5Coeffs = SparsePolynomial.eval (gapValues g) entryA00 * SparsePolynomial.eval (gapValues g) det00Pair5 := by
  rw [det00Term5Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det00Term5Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det00Pair5 = v
  simp only [entryA00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite12
