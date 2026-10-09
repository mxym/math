import APPT.Finite9Sparse.det03Term2Rows00
import APPT.Finite9Sparse.det03Term2Rows01
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term2Coeffs : CoefficientMerge.Poly := [(11, -1), (12, -1), (20, -1), (21, -2), (22, -1), (23, -1), (30, -1), (31, -1), (32, -1), (92, -1), (93, -1), (101, -2), (102, -4), (103, -2), (104, -2), (105, -1), (111, -2), (112, -2), (113, -2), (114, -1), (182, -1), (183, -3), (184, -2), (185, -2), (186, -1), (192, -3), (193, -4), (194, -4), (195, -2), (202, -1), (203, -2), (204, -1), (212, -1), (213, -1), (273, -1), (274, -2), (275, -2), (276, -1), (283, -1), (284, -2), (285, -1), (293, -1), (294, -1)]
theorem det03Term2Coeffs_data : det03Term2Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det03Term2Row00 det03Term2Row01) (CoefficientMerge.fastMerge det03Term2Row02 (CoefficientMerge.fastMerge det03Term2Row03 det03Term2Row04))) := by decide +kernel
theorem eval_det03Term2Coeffs (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term2Coeffs = SparsePolynomial.eval (gapValues g) entryB02 * SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [det03Term2Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term2Row00, eval_det03Term2Row01, eval_det03Term2Row02, eval_det03Term2Row03, eval_det03Term2Row04]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair2 = v
  simp only [entryB02, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite9
