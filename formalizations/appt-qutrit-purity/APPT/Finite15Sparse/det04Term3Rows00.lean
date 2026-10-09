import APPT.Finite15Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term3Row00 : CoefficientMerge.Poly := [(251, 2), (252, 2), (253, 2), (254, 2), (266, 2), (267, 2), (268, 2), (269, 2), (281, 2), (282, 2), (283, 2), (284, 2), (296, 2), (297, 2), (298, 2), (299, 2), (311, 2), (312, 2), (313, 2), (314, 2), (326, 2), (327, 2), (328, 2), (329, 2), (341, 2), (342, 2), (343, 2), (344, 2), (356, 2), (357, 2), (358, 2), (359, 2), (371, 2), (372, 2), (373, 2), (374, 2), (386, 2), (387, 2), (388, 2), (389, 2), (401, 2), (402, 2), (403, 2), (404, 2)]
theorem det04Term3Row00_decode : SparsePolynomial.decodeCubic 15 det04Term3Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row00 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row01 : CoefficientMerge.Poly := [(266, 2), (267, 2), (268, 2), (269, 2), (491, 2), (492, 2), (493, 2), (494, 2), (506, 2), (507, 2), (508, 2), (509, 2), (521, 2), (522, 2), (523, 2), (524, 2), (536, 2), (537, 2), (538, 2), (539, 2), (551, 2), (552, 2), (553, 2), (554, 2), (566, 2), (567, 2), (568, 2), (569, 2), (581, 2), (582, 2), (583, 2), (584, 2), (596, 2), (597, 2), (598, 2), (599, 2), (611, 2), (612, 2), (613, 2), (614, 2), (626, 2), (627, 2), (628, 2), (629, 2)]
theorem det04Term3Row01_decode : SparsePolynomial.decodeCubic 15 det04Term3Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row01 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row02 : CoefficientMerge.Poly := [(281, 2), (282, 2), (283, 2), (284, 2), (506, 2), (507, 2), (508, 2), (509, 2), (731, 2), (732, 2), (733, 2), (734, 2), (746, 2), (747, 2), (748, 2), (749, 2), (761, 2), (762, 2), (763, 2), (764, 2), (776, 2), (777, 2), (778, 2), (779, 2), (791, 2), (792, 2), (793, 2), (794, 2), (806, 2), (807, 2), (808, 2), (809, 2), (821, 2), (822, 2), (823, 2), (824, 2), (836, 2), (837, 2), (838, 2), (839, 2), (851, 2), (852, 2), (853, 2), (854, 2)]
theorem det04Term3Row02_decode : SparsePolynomial.decodeCubic 15 det04Term3Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row02 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row03 : CoefficientMerge.Poly := [(296, 2), (297, 2), (298, 2), (299, 2), (521, 2), (522, 2), (523, 2), (524, 2), (746, 2), (747, 2), (748, 2), (749, 2), (971, 2), (972, 2), (973, 2), (974, 2), (986, 2), (987, 2), (988, 2), (989, 2), (1001, 2), (1002, 2), (1003, 2), (1004, 2), (1016, 2), (1017, 2), (1018, 2), (1019, 2), (1031, 2), (1032, 2), (1033, 2), (1034, 2), (1046, 2), (1047, 2), (1048, 2), (1049, 2), (1061, 2), (1062, 2), (1063, 2), (1064, 2), (1076, 2), (1077, 2), (1078, 2), (1079, 2)]
theorem det04Term3Row03_decode : SparsePolynomial.decodeCubic 15 det04Term3Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row03 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
