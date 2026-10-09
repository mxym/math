import APPT.Finite12Sparse.det00Term3Rows00
import APPT.Finite12Sparse.det00Term3Rows01
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term3Coeffs : CoefficientMerge.Poly := [(165, 2), (166, 2), (167, 2), (177, 4), (178, 4), (179, 4), (189, 4), (190, 4), (191, 4), (201, 4), (202, 4), (203, 4), (213, 4), (214, 4), (215, 4), (225, 4), (226, 4), (227, 4), (237, 4), (238, 4), (239, 4), (321, 2), (322, 2), (323, 2), (333, 4), (334, 4), (335, 4), (345, 4), (346, 4), (347, 4), (357, 4), (358, 4), (359, 4), (369, 4), (370, 4), (371, 4), (381, 4), (382, 4), (383, 4), (477, 2), (478, 2), (479, 2), (489, 4), (490, 4), (491, 4), (501, 4), (502, 4), (503, 4), (513, 4), (514, 4), (515, 4), (525, 4), (526, 4), (527, 4), (633, 2), (634, 2), (635, 2), (645, 4), (646, 4), (647, 4), (657, 4), (658, 4), (659, 4), (669, 4), (670, 4), (671, 4), (789, 2), (790, 2), (791, 2), (801, 4), (802, 4), (803, 4), (813, 4), (814, 4), (815, 4), (945, 2), (946, 2), (947, 2), (957, 4), (958, 4), (959, 4), (1101, 2), (1102, 2), (1103, 2)]
theorem det00Term3Coeffs_data : det00Term3Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det00Term3Row00 (CoefficientMerge.fastMerge det00Term3Row01 det00Term3Row02)) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det00Term3Row03 det00Term3Row04) (CoefficientMerge.fastMerge det00Term3Row05 det00Term3Row06))) := by decide +kernel
theorem eval_det00Term3Coeffs (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Coeffs = SparsePolynomial.eval (gapValues g) entryA02 * SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [det00Term3Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det00Term3Row00, eval_det00Term3Row01, eval_det00Term3Row02, eval_det00Term3Row03, eval_det00Term3Row04, eval_det00Term3Row05, eval_det00Term3Row06]
  generalize hq : SparsePolynomial.eval (gapValues g) det00Pair3 = v
  simp only [entryA02, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite12
