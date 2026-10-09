import APPT.Finite15Sparse.Det00Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term2Row00 : CoefficientMerge.Poly := [(17, -1), (18, -1), (19, -1), (20, -1), (21, -1), (22, -1), (23, -1), (24, -1), (242, -1), (243, -1), (244, -1), (245, -1), (246, -1), (247, -1), (248, -1), (249, -1), (257, -1), (258, -2), (259, -2), (260, -2), (261, -2), (262, -2), (263, -2), (264, -2), (265, -1), (266, -1), (267, -1), (273, -1), (274, -2), (275, -2), (276, -2), (277, -2), (278, -2), (279, -2), (280, -1), (281, -1), (282, -1), (289, -1), (290, -2), (291, -2), (292, -2), (293, -2), (294, -2), (295, -1), (296, -1), (297, -1), (305, -1), (306, -2), (307, -2), (308, -2), (309, -2), (310, -1), (311, -1), (312, -1), (321, -1), (322, -2), (323, -2), (324, -2), (325, -1), (326, -1), (327, -1), (337, -1), (338, -2), (339, -2), (340, -1), (341, -1), (342, -1), (353, -1), (354, -2), (355, -1), (356, -1), (357, -1), (369, -1), (370, -1), (371, -1), (372, -1)]
theorem det00Term2Row00_decode : SparsePolynomial.decodeCubic 15 det00Term2Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row00 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term2Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term2Row01 : CoefficientMerge.Poly := [(32, -1), (33, -1), (34, -1), (35, -1), (36, -1), (37, -1), (38, -1), (39, -1), (257, -1), (258, -1), (259, -1), (260, -1), (261, -1), (262, -1), (263, -1), (264, -1), (482, -1), (483, -2), (484, -2), (485, -2), (486, -2), (487, -2), (488, -2), (489, -2), (490, -1), (491, -1), (492, -1), (498, -1), (499, -2), (500, -2), (501, -2), (502, -2), (503, -2), (504, -2), (505, -1), (506, -1), (507, -1), (514, -1), (515, -2), (516, -2), (517, -2), (518, -2), (519, -2), (520, -1), (521, -1), (522, -1), (530, -1), (531, -2), (532, -2), (533, -2), (534, -2), (535, -1), (536, -1), (537, -1), (546, -1), (547, -2), (548, -2), (549, -2), (550, -1), (551, -1), (552, -1), (562, -1), (563, -2), (564, -2), (565, -1), (566, -1), (567, -1), (578, -1), (579, -2), (580, -1), (581, -1), (582, -1), (594, -1), (595, -1), (596, -1), (597, -1)]
theorem det00Term2Row01_decode : SparsePolynomial.decodeCubic 15 det00Term2Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row01 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term2Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term2Row02 : CoefficientMerge.Poly := [(33, -1), (48, -1), (49, -1), (50, -1), (51, -1), (52, -1), (53, -1), (54, -1), (258, -1), (273, -1), (274, -1), (275, -1), (276, -1), (277, -1), (278, -1), (279, -1), (483, -1), (498, -2), (499, -2), (500, -2), (501, -2), (502, -2), (503, -2), (504, -2), (505, -1), (506, -1), (507, -1), (723, -1), (724, -2), (725, -2), (726, -2), (727, -2), (728, -2), (729, -2), (730, -1), (731, -1), (732, -1), (739, -1), (740, -2), (741, -2), (742, -2), (743, -2), (744, -2), (745, -1), (746, -1), (747, -1), (755, -1), (756, -2), (757, -2), (758, -2), (759, -2), (760, -1), (761, -1), (762, -1), (771, -1), (772, -2), (773, -2), (774, -2), (775, -1), (776, -1), (777, -1), (787, -1), (788, -2), (789, -2), (790, -1), (791, -1), (792, -1), (803, -1), (804, -2), (805, -1), (806, -1), (807, -1), (819, -1), (820, -1), (821, -1), (822, -1)]
theorem det00Term2Row02_decode : SparsePolynomial.decodeCubic 15 det00Term2Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row02 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term2Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term2Row03 : CoefficientMerge.Poly := [(34, -1), (49, -1), (64, -1), (65, -1), (66, -1), (67, -1), (68, -1), (69, -1), (259, -1), (274, -1), (289, -1), (290, -1), (291, -1), (292, -1), (293, -1), (294, -1), (484, -1), (499, -2), (514, -2), (515, -2), (516, -2), (517, -2), (518, -2), (519, -2), (520, -1), (521, -1), (522, -1), (724, -1), (739, -2), (740, -2), (741, -2), (742, -2), (743, -2), (744, -2), (745, -1), (746, -1), (747, -1), (964, -1), (965, -2), (966, -2), (967, -2), (968, -2), (969, -2), (970, -1), (971, -1), (972, -1), (980, -1), (981, -2), (982, -2), (983, -2), (984, -2), (985, -1), (986, -1), (987, -1), (996, -1), (997, -2), (998, -2), (999, -2), (1000, -1), (1001, -1), (1002, -1), (1012, -1), (1013, -2), (1014, -2), (1015, -1), (1016, -1), (1017, -1), (1028, -1), (1029, -2), (1030, -1), (1031, -1), (1032, -1), (1044, -1), (1045, -1), (1046, -1), (1047, -1)]
theorem det00Term2Row03_decode : SparsePolynomial.decodeCubic 15 det00Term2Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row03 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term2Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
