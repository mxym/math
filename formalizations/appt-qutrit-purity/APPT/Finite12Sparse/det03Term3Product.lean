import APPT.Finite12Sparse.det03Term3Rows00
import APPT.Finite12Sparse.det03Term3Rows01
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term3Coeffs : CoefficientMerge.Poly := [(164, 2), (165, 2), (166, 2), (167, 2), (176, 4), (177, 4), (178, 4), (179, 4), (188, 4), (189, 4), (190, 4), (191, 4), (200, 4), (201, 4), (202, 4), (203, 4), (212, 4), (213, 4), (214, 4), (215, 4), (224, 4), (225, 4), (226, 4), (227, 4), (236, 4), (237, 4), (238, 4), (239, 4), (248, 4), (249, 4), (250, 4), (251, 4), (320, 2), (321, 2), (322, 2), (323, 2), (332, 4), (333, 4), (334, 4), (335, 4), (344, 4), (345, 4), (346, 4), (347, 4), (356, 4), (357, 4), (358, 4), (359, 4), (368, 4), (369, 4), (370, 4), (371, 4), (380, 4), (381, 4), (382, 4), (383, 4), (392, 4), (393, 4), (394, 4), (395, 4), (476, 2), (477, 2), (478, 2), (479, 2), (488, 4), (489, 4), (490, 4), (491, 4), (500, 4), (501, 4), (502, 4), (503, 4), (512, 4), (513, 4), (514, 4), (515, 4), (524, 4), (525, 4), (526, 4), (527, 4), (536, 4), (537, 4), (538, 4), (539, 4), (632, 2), (633, 2), (634, 2), (635, 2), (644, 4), (645, 4), (646, 4), (647, 4), (656, 4), (657, 4), (658, 4), (659, 4), (668, 4), (669, 4), (670, 4), (671, 4), (680, 4), (681, 4), (682, 4), (683, 4), (788, 2), (789, 2), (790, 2), (791, 2), (800, 4), (801, 4), (802, 4), (803, 4), (812, 4), (813, 4), (814, 4), (815, 4), (824, 4), (825, 4), (826, 4), (827, 4), (944, 2), (945, 2), (946, 2), (947, 2), (956, 4), (957, 4), (958, 4), (959, 4), (968, 4), (969, 4), (970, 4), (971, 4), (1100, 2), (1101, 2), (1102, 2), (1103, 2), (1112, 4), (1113, 4), (1114, 4), (1115, 4), (1256, 2), (1257, 2), (1258, 2), (1259, 2)]
theorem det03Term3Coeffs_data : det03Term3Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det03Term3Row00 det03Term3Row01) (CoefficientMerge.fastMerge det03Term3Row02 det03Term3Row03)) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det03Term3Row04 det03Term3Row05) (CoefficientMerge.fastMerge det03Term3Row06 det03Term3Row07))) := by decide +kernel
theorem eval_det03Term3Coeffs (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term3Coeffs = SparsePolynomial.eval (gapValues g) entryB02 * SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [det03Term3Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term3Row00, eval_det03Term3Row01, eval_det03Term3Row02, eval_det03Term3Row03, eval_det03Term3Row04, eval_det03Term3Row05, eval_det03Term3Row06, eval_det03Term3Row07]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair3 = v
  simp only [entryB02, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite12
