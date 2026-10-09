import APPT.Finite12Sparse.Det03Pair4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term4Row00 : CoefficientMerge.Poly := [(6, 2), (7, 2), (8, 2), (9, 2), (10, 2), (11, 2), (18, 2), (19, 2), (20, 2), (21, 2), (22, 2), (23, 2), (30, 2), (31, 2), (32, 2), (33, 2), (34, 2), (35, 2), (42, 2), (43, 2), (44, 2), (45, 2), (46, 2), (47, 2), (54, 2), (55, 2), (56, 2), (57, 2), (58, 2), (59, 2), (66, 2), (67, 2), (68, 2), (69, 2), (70, 2), (71, 2), (78, 2), (79, 4), (80, 4), (81, 4), (82, 2), (83, 2), (91, 2), (92, 4), (93, 4), (94, 2), (95, 2), (104, 2), (105, 4), (106, 2), (107, 2), (117, 2), (118, 2), (119, 2)]
theorem det03Term4Row00_decode : SparsePolynomial.decodeCubic 12 det03Term4Row00 = SparsePolynomial.monoTimes [0] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row00 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term4Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [0]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term4Row01 : CoefficientMerge.Poly := [(18, 2), (19, 2), (20, 2), (21, 2), (22, 2), (23, 2), (162, 2), (163, 2), (164, 2), (165, 2), (166, 2), (167, 2), (174, 2), (175, 2), (176, 2), (177, 2), (178, 2), (179, 2), (186, 2), (187, 2), (188, 2), (189, 2), (190, 2), (191, 2), (198, 2), (199, 2), (200, 2), (201, 2), (202, 2), (203, 2), (210, 2), (211, 2), (212, 2), (213, 2), (214, 2), (215, 2), (222, 2), (223, 4), (224, 4), (225, 4), (226, 2), (227, 2), (235, 2), (236, 4), (237, 4), (238, 2), (239, 2), (248, 2), (249, 4), (250, 2), (251, 2), (261, 2), (262, 2), (263, 2)]
theorem det03Term4Row01_decode : SparsePolynomial.decodeCubic 12 det03Term4Row01 = SparsePolynomial.monoTimes [1] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row01 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term4Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term4Row02 : CoefficientMerge.Poly := [(30, 2), (31, 2), (32, 2), (33, 2), (34, 2), (35, 2), (174, 2), (175, 2), (176, 2), (177, 2), (178, 2), (179, 2), (318, 2), (319, 2), (320, 2), (321, 2), (322, 2), (323, 2), (330, 2), (331, 2), (332, 2), (333, 2), (334, 2), (335, 2), (342, 2), (343, 2), (344, 2), (345, 2), (346, 2), (347, 2), (354, 2), (355, 2), (356, 2), (357, 2), (358, 2), (359, 2), (366, 2), (367, 4), (368, 4), (369, 4), (370, 2), (371, 2), (379, 2), (380, 4), (381, 4), (382, 2), (383, 2), (392, 2), (393, 4), (394, 2), (395, 2), (405, 2), (406, 2), (407, 2)]
theorem det03Term4Row02_decode : SparsePolynomial.decodeCubic 12 det03Term4Row02 = SparsePolynomial.monoTimes [2] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row02 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term4Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term4Row03 : CoefficientMerge.Poly := [(42, 2), (43, 2), (44, 2), (45, 2), (46, 2), (47, 2), (186, 2), (187, 2), (188, 2), (189, 2), (190, 2), (191, 2), (330, 2), (331, 2), (332, 2), (333, 2), (334, 2), (335, 2), (474, 2), (475, 2), (476, 2), (477, 2), (478, 2), (479, 2), (486, 2), (487, 2), (488, 2), (489, 2), (490, 2), (491, 2), (498, 2), (499, 2), (500, 2), (501, 2), (502, 2), (503, 2), (510, 2), (511, 4), (512, 4), (513, 4), (514, 2), (515, 2), (523, 2), (524, 4), (525, 4), (526, 2), (527, 2), (536, 2), (537, 4), (538, 2), (539, 2), (549, 2), (550, 2), (551, 2)]
theorem det03Term4Row03_decode : SparsePolynomial.decodeCubic 12 det03Term4Row03 = SparsePolynomial.monoTimes [3] (-1 : Int) det03Pair4 := by decide +kernel
theorem eval_det03Term4Row03 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term4Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det03Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term4Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
