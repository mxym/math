import APPT.Finite12Sparse.det00Term2Rows00
import APPT.Finite12Sparse.det00Term2Rows01
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term2Coeffs : CoefficientMerge.Poly := [(14, -1), (15, -1), (16, -1), (17, -1), (18, -1), (26, -1), (27, -2), (28, -2), (29, -2), (30, -2), (31, -1), (39, -1), (40, -2), (41, -2), (42, -2), (43, -1), (52, -1), (53, -2), (54, -2), (55, -1), (65, -1), (66, -2), (67, -1), (78, -1), (79, -1), (158, -1), (159, -1), (160, -1), (161, -1), (162, -1), (170, -2), (171, -4), (172, -4), (173, -4), (174, -4), (175, -2), (176, -1), (177, -1), (183, -2), (184, -4), (185, -4), (186, -4), (187, -2), (188, -1), (189, -1), (196, -2), (197, -4), (198, -4), (199, -2), (200, -1), (201, -1), (209, -2), (210, -4), (211, -2), (212, -1), (213, -1), (222, -2), (223, -2), (224, -1), (225, -1), (314, -1), (315, -3), (316, -3), (317, -3), (318, -3), (319, -2), (320, -1), (321, -1), (327, -3), (328, -6), (329, -6), (330, -6), (331, -4), (332, -2), (333, -2), (340, -3), (341, -6), (342, -6), (343, -4), (344, -2), (345, -2), (353, -3), (354, -6), (355, -4), (356, -2), (357, -2), (366, -3), (367, -4), (368, -2), (369, -2), (379, -1), (380, -1), (381, -1), (471, -1), (472, -3), (473, -3), (474, -3), (475, -2), (476, -1), (477, -1), (484, -3), (485, -6), (486, -6), (487, -4), (488, -2), (489, -2), (497, -3), (498, -6), (499, -4), (500, -2), (501, -2), (510, -3), (511, -4), (512, -2), (513, -2), (523, -1), (524, -1), (525, -1), (628, -1), (629, -3), (630, -3), (631, -2), (632, -1), (633, -1), (641, -3), (642, -6), (643, -4), (644, -2), (645, -2), (654, -3), (655, -4), (656, -2), (657, -2), (667, -1), (668, -1), (669, -1), (785, -1), (786, -3), (787, -2), (788, -1), (789, -1), (798, -3), (799, -4), (800, -2), (801, -2), (811, -1), (812, -1), (813, -1), (942, -1), (943, -2), (944, -1), (945, -1), (955, -1), (956, -1), (957, -1)]
theorem det00Term2Coeffs_data : det00Term2Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det00Term2Row00 (CoefficientMerge.fastMerge det00Term2Row01 det00Term2Row02)) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det00Term2Row03 det00Term2Row04) (CoefficientMerge.fastMerge det00Term2Row05 det00Term2Row06))) := by decide +kernel
theorem eval_det00Term2Coeffs (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term2Coeffs = SparsePolynomial.eval (gapValues g) entryA02 * SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [det00Term2Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det00Term2Row00, eval_det00Term2Row01, eval_det00Term2Row02, eval_det00Term2Row03, eval_det00Term2Row04, eval_det00Term2Row05, eval_det00Term2Row06]
  generalize hq : SparsePolynomial.eval (gapValues g) det00Pair2 = v
  simp only [entryA02, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite12
