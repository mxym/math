import APPT.Finite12Sparse.det03Term4Rows00
import APPT.Finite12Sparse.det03Term4Rows01
import APPT.Finite12Sparse.det03Term4Rows02
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term4Coeffs : CoefficientMerge.Poly := [(6, 2), (7, 2), (8, 2), (9, 2), (10, 2), (11, 2), (18, 4), (19, 4), (20, 4), (21, 4), (22, 4), (23, 4), (30, 4), (31, 4), (32, 4), (33, 4), (34, 4), (35, 4), (42, 4), (43, 4), (44, 4), (45, 4), (46, 4), (47, 4), (54, 4), (55, 4), (56, 4), (57, 4), (58, 4), (59, 4), (66, 4), (67, 4), (68, 4), (69, 4), (70, 4), (71, 4), (78, 4), (79, 8), (80, 8), (81, 8), (82, 4), (83, 4), (91, 4), (92, 8), (93, 8), (94, 4), (95, 4), (104, 4), (105, 8), (106, 4), (107, 4), (117, 4), (118, 4), (119, 4), (162, 2), (163, 2), (164, 2), (165, 2), (166, 2), (167, 2), (174, 4), (175, 4), (176, 4), (177, 4), (178, 4), (179, 4), (186, 4), (187, 4), (188, 4), (189, 4), (190, 4), (191, 4), (198, 4), (199, 4), (200, 4), (201, 4), (202, 4), (203, 4), (210, 4), (211, 4), (212, 4), (213, 4), (214, 4), (215, 4), (222, 4), (223, 8), (224, 8), (225, 8), (226, 4), (227, 4), (235, 4), (236, 8), (237, 8), (238, 4), (239, 4), (248, 4), (249, 8), (250, 4), (251, 4), (261, 4), (262, 4), (263, 4), (318, 2), (319, 2), (320, 2), (321, 2), (322, 2), (323, 2), (330, 4), (331, 4), (332, 4), (333, 4), (334, 4), (335, 4), (342, 4), (343, 4), (344, 4), (345, 4), (346, 4), (347, 4), (354, 4), (355, 4), (356, 4), (357, 4), (358, 4), (359, 4), (366, 4), (367, 8), (368, 8), (369, 8), (370, 4), (371, 4), (379, 4), (380, 8), (381, 8), (382, 4), (383, 4), (392, 4), (393, 8), (394, 4), (395, 4), (405, 4), (406, 4), (407, 4), (474, 2), (475, 2), (476, 2), (477, 2), (478, 2), (479, 2), (486, 4), (487, 4), (488, 4), (489, 4), (490, 4), (491, 4), (498, 4), (499, 4), (500, 4), (501, 4), (502, 4), (503, 4), (510, 4), (511, 8), (512, 8), (513, 8), (514, 4), (515, 4), (523, 4), (524, 8), (525, 8), (526, 4), (527, 4), (536, 4), (537, 8), (538, 4), (539, 4), (549, 4), (550, 4), (551, 4), (630, 2), (631, 2), (632, 2), (633, 2), (634, 2), (635, 2), (642, 4), (643, 4), (644, 4), (645, 4), (646, 4), (647, 4), (654, 4), (655, 8), (656, 8), (657, 8), (658, 4), (659, 4), (667, 4), (668, 8), (669, 8), (670, 4), (671, 4), (680, 4), (681, 8), (682, 4), (683, 4), (693, 4), (694, 4), (695, 4), (786, 2), (787, 2), (788, 2), (789, 2), (790, 2), (791, 2), (798, 4), (799, 8), (800, 8), (801, 8), (802, 4), (803, 4), (811, 4), (812, 8), (813, 8), (814, 4), (815, 4), (824, 4), (825, 8), (826, 4), (827, 4), (837, 4), (838, 4), (839, 4), (942, 2), (943, 6), (944, 6), (945, 6), (946, 2), (947, 2), (955, 6), (956, 12), (957, 12), (958, 4), (959, 4), (968, 6), (969, 12), (970, 4), (971, 4), (981, 6), (982, 4), (983, 4), (1099, 2), (1100, 6), (1101, 6), (1102, 2), (1103, 2), (1112, 6), (1113, 12), (1114, 4), (1115, 4), (1125, 6), (1126, 4), (1127, 4), (1256, 2), (1257, 6), (1258, 2), (1259, 2), (1269, 6), (1270, 4), (1271, 4), (1413, 2), (1414, 2), (1415, 2)]
theorem det03Term4Coeffs_data : det03Term4Coeffs = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det03Term4Row00 det03Term4Row01) (CoefficientMerge.fastMerge det03Term4Row02 (CoefficientMerge.fastMerge det03Term4Row03 det03Term4Row04))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge det03Term4Row05 det03Term4Row06) (CoefficientMerge.fastMerge det03Term4Row07 (CoefficientMerge.fastMerge det03Term4Row08 det03Term4Row09)))) := by decide +kernel
theorem eval_det03Term4Coeffs (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term4Coeffs = SparsePolynomial.eval (gapValues g) entryB01 * SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [det03Term4Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term4Row00, eval_det03Term4Row01, eval_det03Term4Row02, eval_det03Term4Row03, eval_det03Term4Row04, eval_det03Term4Row05, eval_det03Term4Row06, eval_det03Term4Row07, eval_det03Term4Row08, eval_det03Term4Row09]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair4 = v
  simp only [entryB01, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite12
