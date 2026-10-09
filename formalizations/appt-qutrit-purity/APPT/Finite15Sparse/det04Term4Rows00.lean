import APPT.Finite15Sparse.Det04Pair4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term4Row00 : CoefficientMerge.Poly := [(9, 2), (10, 2), (11, 2), (12, 2), (13, 2), (14, 2), (24, 2), (25, 2), (26, 2), (27, 2), (28, 2), (29, 2), (39, 2), (40, 2), (41, 2), (42, 2), (43, 2), (44, 2), (54, 2), (55, 2), (56, 2), (57, 2), (58, 2), (59, 2), (69, 2), (70, 2), (71, 2), (72, 2), (73, 2), (74, 2), (84, 2), (85, 2), (86, 2), (87, 2), (88, 2), (89, 2), (99, 2), (100, 2), (101, 2), (102, 2), (103, 2), (104, 2), (114, 2), (115, 2), (116, 2), (117, 2), (118, 2), (119, 2), (129, 2), (130, 2), (131, 2), (132, 2), (133, 2), (134, 2), (144, 2), (145, 4), (146, 4), (147, 4), (148, 2), (149, 2), (160, 2), (161, 4), (162, 4), (163, 2), (164, 2), (176, 2), (177, 4), (178, 2), (179, 2), (192, 2), (193, 2), (194, 2)]
theorem det04Term4Row00_decode : SparsePolynomial.decodeCubic 15 det04Term4Row00 = SparsePolynomial.monoTimes [0] (-1 : Int) det04Pair4 := by decide +kernel
theorem eval_det04Term4Row00 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term4Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [0]*SparsePolynomial.eval (gapValues g) det04Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term4Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term4Row01 : CoefficientMerge.Poly := [(24, 2), (25, 2), (26, 2), (27, 2), (28, 2), (29, 2), (249, 2), (250, 2), (251, 2), (252, 2), (253, 2), (254, 2), (264, 2), (265, 2), (266, 2), (267, 2), (268, 2), (269, 2), (279, 2), (280, 2), (281, 2), (282, 2), (283, 2), (284, 2), (294, 2), (295, 2), (296, 2), (297, 2), (298, 2), (299, 2), (309, 2), (310, 2), (311, 2), (312, 2), (313, 2), (314, 2), (324, 2), (325, 2), (326, 2), (327, 2), (328, 2), (329, 2), (339, 2), (340, 2), (341, 2), (342, 2), (343, 2), (344, 2), (354, 2), (355, 2), (356, 2), (357, 2), (358, 2), (359, 2), (369, 2), (370, 4), (371, 4), (372, 4), (373, 2), (374, 2), (385, 2), (386, 4), (387, 4), (388, 2), (389, 2), (401, 2), (402, 4), (403, 2), (404, 2), (417, 2), (418, 2), (419, 2)]
theorem det04Term4Row01_decode : SparsePolynomial.decodeCubic 15 det04Term4Row01 = SparsePolynomial.monoTimes [1] (-1 : Int) det04Pair4 := by decide +kernel
theorem eval_det04Term4Row01 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term4Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det04Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term4Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term4Row02 : CoefficientMerge.Poly := [(39, 2), (40, 2), (41, 2), (42, 2), (43, 2), (44, 2), (264, 2), (265, 2), (266, 2), (267, 2), (268, 2), (269, 2), (489, 2), (490, 2), (491, 2), (492, 2), (493, 2), (494, 2), (504, 2), (505, 2), (506, 2), (507, 2), (508, 2), (509, 2), (519, 2), (520, 2), (521, 2), (522, 2), (523, 2), (524, 2), (534, 2), (535, 2), (536, 2), (537, 2), (538, 2), (539, 2), (549, 2), (550, 2), (551, 2), (552, 2), (553, 2), (554, 2), (564, 2), (565, 2), (566, 2), (567, 2), (568, 2), (569, 2), (579, 2), (580, 2), (581, 2), (582, 2), (583, 2), (584, 2), (594, 2), (595, 4), (596, 4), (597, 4), (598, 2), (599, 2), (610, 2), (611, 4), (612, 4), (613, 2), (614, 2), (626, 2), (627, 4), (628, 2), (629, 2), (642, 2), (643, 2), (644, 2)]
theorem det04Term4Row02_decode : SparsePolynomial.decodeCubic 15 det04Term4Row02 = SparsePolynomial.monoTimes [2] (-1 : Int) det04Pair4 := by decide +kernel
theorem eval_det04Term4Row02 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term4Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det04Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term4Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term4Row03 : CoefficientMerge.Poly := [(54, 2), (55, 2), (56, 2), (57, 2), (58, 2), (59, 2), (279, 2), (280, 2), (281, 2), (282, 2), (283, 2), (284, 2), (504, 2), (505, 2), (506, 2), (507, 2), (508, 2), (509, 2), (729, 2), (730, 2), (731, 2), (732, 2), (733, 2), (734, 2), (744, 2), (745, 2), (746, 2), (747, 2), (748, 2), (749, 2), (759, 2), (760, 2), (761, 2), (762, 2), (763, 2), (764, 2), (774, 2), (775, 2), (776, 2), (777, 2), (778, 2), (779, 2), (789, 2), (790, 2), (791, 2), (792, 2), (793, 2), (794, 2), (804, 2), (805, 2), (806, 2), (807, 2), (808, 2), (809, 2), (819, 2), (820, 4), (821, 4), (822, 4), (823, 2), (824, 2), (835, 2), (836, 4), (837, 4), (838, 2), (839, 2), (851, 2), (852, 4), (853, 2), (854, 2), (867, 2), (868, 2), (869, 2)]
theorem det04Term4Row03_decode : SparsePolynomial.decodeCubic 15 det04Term4Row03 = SparsePolynomial.monoTimes [3] (-1 : Int) det04Pair4 := by decide +kernel
theorem eval_det04Term4Row03 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term4Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det04Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term4Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
