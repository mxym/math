import APPT.Finite12Sparse.det03Term1Rows00
import APPT.Finite12Sparse.det03Term1Rows01
import APPT.Finite12Sparse.det03Term1Rows02
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term1Coeffs : CoefficientMerge.Poly := [(14, -1), (15, -1), (16, -1), (17, -1), (18, -1), (26, -1), (27, -2), (28, -2), (29, -2), (30, -2), (31, -1), (32, -1), (39, -1), (40, -2), (41, -2), (42, -2), (43, -1), (44, -1), (52, -1), (53, -2), (54, -2), (55, -1), (56, -1), (65, -1), (66, -2), (67, -1), (68, -1), (78, -1), (79, -1), (80, -1), (158, -1), (159, -1), (160, -1), (161, -1), (162, -1), (170, -2), (171, -4), (172, -4), (173, -4), (174, -4), (175, -2), (176, -2), (177, -1), (183, -2), (184, -4), (185, -4), (186, -4), (187, -2), (188, -2), (189, -1), (196, -2), (197, -4), (198, -4), (199, -2), (200, -2), (201, -1), (209, -2), (210, -4), (211, -2), (212, -2), (213, -1), (222, -2), (223, -2), (224, -2), (225, -1), (314, -1), (315, -3), (316, -3), (317, -3), (318, -3), (319, -2), (320, -2), (321, -1), (327, -3), (328, -6), (329, -6), (330, -6), (331, -4), (332, -4), (333, -2), (340, -3), (341, -6), (342, -6), (343, -4), (344, -4), (345, -2), (353, -3), (354, -6), (355, -4), (356, -4), (357, -2), (366, -3), (367, -4), (368, -4), (369, -2), (379, -1), (380, -2), (381, -1), (392, -1), (393, -1), (471, -1), (472, -3), (473, -3), (474, -3), (475, -2), (476, -2), (477, -1), (484, -3), (485, -6), (486, -6), (487, -4), (488, -4), (489, -2), (497, -3), (498, -6), (499, -4), (500, -4), (501, -2), (510, -3), (511, -4), (512, -4), (513, -2), (523, -1), (524, -2), (525, -1), (536, -1), (537, -1), (628, -1), (629, -3), (630, -3), (631, -2), (632, -2), (633, -1), (641, -3), (642, -6), (643, -4), (644, -4), (645, -2), (654, -3), (655, -4), (656, -4), (657, -2), (667, -1), (668, -2), (669, -1), (680, -1), (681, -1), (785, -1), (786, -3), (787, -2), (788, -2), (789, -1), (798, -3), (799, -4), (800, -4), (801, -2), (811, -1), (812, -2), (813, -1), (824, -1), (825, -1), (942, -1), (943, -2), (944, -2), (945, -1), (955, -1), (956, -2), (957, -1), (968, -1), (969, -1)]
theorem det03Term1Coeffs_data : det03Term1Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det03Term1Row00 det03Term1Row01) (CoefficientMerge.fastMerge det03Term1Row02 (CoefficientMerge.fastMerge det03Term1Row03 det03Term1Row04))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det03Term1Row05 det03Term1Row06) (CoefficientMerge.fastMerge det03Term1Row07 (CoefficientMerge.fastMerge det03Term1Row08 det03Term1Row09)))) := by decide +kernel
theorem eval_det03Term1Coeffs (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term1Coeffs = SparsePolynomial.eval (gapValues g) entryB01 * SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [det03Term1Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term1Row00, eval_det03Term1Row01, eval_det03Term1Row02, eval_det03Term1Row03, eval_det03Term1Row04, eval_det03Term1Row05, eval_det03Term1Row06, eval_det03Term1Row07, eval_det03Term1Row08, eval_det03Term1Row09]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair1 = v
  simp only [entryB01, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite12
