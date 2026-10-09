import APPT.Finite12Sparse.Det03Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term3Row00 : CoefficientMerge.Poly := [(164, 2), (165, 2), (166, 2), (167, 2), (176, 2), (177, 2), (178, 2), (179, 2), (188, 2), (189, 2), (190, 2), (191, 2), (200, 2), (201, 2), (202, 2), (203, 2), (212, 2), (213, 2), (214, 2), (215, 2), (224, 2), (225, 2), (226, 2), (227, 2), (236, 2), (237, 2), (238, 2), (239, 2), (248, 2), (249, 2), (250, 2), (251, 2)]
theorem det03Term3Row00_decode : SparsePolynomial.decodeCubic 12 det03Term3Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row00 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term3Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row01 : CoefficientMerge.Poly := [(176, 2), (177, 2), (178, 2), (179, 2), (320, 2), (321, 2), (322, 2), (323, 2), (332, 2), (333, 2), (334, 2), (335, 2), (344, 2), (345, 2), (346, 2), (347, 2), (356, 2), (357, 2), (358, 2), (359, 2), (368, 2), (369, 2), (370, 2), (371, 2), (380, 2), (381, 2), (382, 2), (383, 2), (392, 2), (393, 2), (394, 2), (395, 2)]
theorem det03Term3Row01_decode : SparsePolynomial.decodeCubic 12 det03Term3Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row01 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term3Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row02 : CoefficientMerge.Poly := [(188, 2), (189, 2), (190, 2), (191, 2), (332, 2), (333, 2), (334, 2), (335, 2), (476, 2), (477, 2), (478, 2), (479, 2), (488, 2), (489, 2), (490, 2), (491, 2), (500, 2), (501, 2), (502, 2), (503, 2), (512, 2), (513, 2), (514, 2), (515, 2), (524, 2), (525, 2), (526, 2), (527, 2), (536, 2), (537, 2), (538, 2), (539, 2)]
theorem det03Term3Row02_decode : SparsePolynomial.decodeCubic 12 det03Term3Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row02 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term3Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row03 : CoefficientMerge.Poly := [(200, 2), (201, 2), (202, 2), (203, 2), (344, 2), (345, 2), (346, 2), (347, 2), (488, 2), (489, 2), (490, 2), (491, 2), (632, 2), (633, 2), (634, 2), (635, 2), (644, 2), (645, 2), (646, 2), (647, 2), (656, 2), (657, 2), (658, 2), (659, 2), (668, 2), (669, 2), (670, 2), (671, 2), (680, 2), (681, 2), (682, 2), (683, 2)]
theorem det03Term3Row03_decode : SparsePolynomial.decodeCubic 12 det03Term3Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row03 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term3Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
