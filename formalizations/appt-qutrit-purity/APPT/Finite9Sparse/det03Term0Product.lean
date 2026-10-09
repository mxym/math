import APPT.Finite9Sparse.det03Term0Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term0Coeffs : CoefficientMerge.Poly := [(296, 8), (305, 8), (314, 8), (323, 8), (377, 8), (386, 8), (395, 8), (404, 8), (458, 8), (467, 16), (476, 16), (485, 16), (548, 8), (557, 16), (566, 16), (638, 8), (647, 16), (728, 8)]
theorem det03Term0Coeffs_data : det03Term0Coeffs = CoefficientMerge.trim det03Term0Row00 := by decide +kernel
theorem eval_det03Term0Coeffs (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term0Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det03Pair0 := by
  rw [det03Term0Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term0Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair0 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite9
