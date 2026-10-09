import APPT.Finite9Sparse.det00Term1Rows00
import APPT.Finite9Sparse.det00Term1Rows01
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Term1Coeffs : CoefficientMerge.Poly := [(11, -1), (12, -1), (20, -1), (21, -2), (22, -1), (30, -1), (31, -1), (92, -1), (93, -1), (101, -2), (102, -4), (103, -2), (104, -1), (105, -1), (111, -2), (112, -2), (113, -1), (114, -1), (182, -1), (183, -3), (184, -2), (185, -1), (186, -1), (192, -3), (193, -4), (194, -2), (195, -2), (202, -1), (203, -1), (204, -1), (273, -1), (274, -2), (275, -1), (276, -1), (283, -1), (284, -1), (285, -1)]
theorem det00Term1Coeffs_data : det00Term1Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det00Term1Row00 (CoefficientMerge.fastMerge det00Term1Row01 det00Term1Row02)) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det00Term1Row03 det00Term1Row04) (CoefficientMerge.fastMerge det00Term1Row05 det00Term1Row06))) := by decide +kernel
theorem eval_det00Term1Coeffs (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term1Coeffs = SparsePolynomial.eval (gapValues g) entryA01 * SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [det00Term1Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det00Term1Row00, eval_det00Term1Row01, eval_det00Term1Row02, eval_det00Term1Row03, eval_det00Term1Row04, eval_det00Term1Row05, eval_det00Term1Row06]
  generalize hq : SparsePolynomial.eval (gapValues g) det00Pair1 = v
  simp only [entryA01, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite9
