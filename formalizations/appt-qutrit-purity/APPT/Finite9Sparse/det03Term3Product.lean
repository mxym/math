import APPT.Finite9Sparse.det03Term3Rows00
import APPT.Finite9Sparse.det03Term3Rows01
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term3Coeffs : CoefficientMerge.Poly := [(95, 2), (96, 2), (97, 2), (98, 2), (104, 4), (105, 4), (106, 4), (107, 4), (113, 4), (114, 4), (115, 4), (116, 4), (122, 4), (123, 4), (124, 4), (125, 4), (131, 4), (132, 4), (133, 4), (134, 4), (185, 2), (186, 2), (187, 2), (188, 2), (194, 4), (195, 4), (196, 4), (197, 4), (203, 4), (204, 4), (205, 4), (206, 4), (212, 4), (213, 4), (214, 4), (215, 4), (275, 2), (276, 2), (277, 2), (278, 2), (284, 4), (285, 4), (286, 4), (287, 4), (293, 4), (294, 4), (295, 4), (296, 4), (365, 2), (366, 2), (367, 2), (368, 2), (374, 4), (375, 4), (376, 4), (377, 4), (455, 2), (456, 2), (457, 2), (458, 2)]
theorem det03Term3Coeffs_data : det03Term3Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det03Term3Row00 det03Term3Row01) (CoefficientMerge.fastMerge det03Term3Row02 (CoefficientMerge.fastMerge det03Term3Row03 det03Term3Row04))) := by decide +kernel
theorem eval_det03Term3Coeffs (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term3Coeffs = SparsePolynomial.eval (gapValues g) entryB02 * SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [det03Term3Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term3Row00, eval_det03Term3Row01, eval_det03Term3Row02, eval_det03Term3Row03, eval_det03Term3Row04]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair3 = v
  simp only [entryB02, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite9
