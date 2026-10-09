import APPT.Finite15Sparse.Det00Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term1Row00 : CoefficientMerge.Poly := [(17, -1), (18, -1), (19, -1), (20, -1), (21, -1), (22, -1), (23, -1), (24, -1), (32, -1), (33, -2), (34, -2), (35, -2), (36, -2), (37, -2), (38, -2), (39, -2), (40, -1), (48, -1), (49, -2), (50, -2), (51, -2), (52, -2), (53, -2), (54, -2), (55, -1), (64, -1), (65, -2), (66, -2), (67, -2), (68, -2), (69, -2), (70, -1), (80, -1), (81, -2), (82, -2), (83, -2), (84, -2), (85, -1), (96, -1), (97, -2), (98, -2), (99, -2), (100, -1), (112, -1), (113, -2), (114, -2), (115, -1), (128, -1), (129, -2), (130, -1), (144, -1), (145, -1)]
theorem det00Term1Row00_decode : SparsePolynomial.decodeCubic 15 det00Term1Row00 = SparsePolynomial.monoTimes [0] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row00 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term1Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [0]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row01 : CoefficientMerge.Poly := [(242, -1), (243, -1), (244, -1), (245, -1), (246, -1), (247, -1), (248, -1), (249, -1), (257, -1), (258, -2), (259, -2), (260, -2), (261, -2), (262, -2), (263, -2), (264, -2), (265, -1), (273, -1), (274, -2), (275, -2), (276, -2), (277, -2), (278, -2), (279, -2), (280, -1), (289, -1), (290, -2), (291, -2), (292, -2), (293, -2), (294, -2), (295, -1), (305, -1), (306, -2), (307, -2), (308, -2), (309, -2), (310, -1), (321, -1), (322, -2), (323, -2), (324, -2), (325, -1), (337, -1), (338, -2), (339, -2), (340, -1), (353, -1), (354, -2), (355, -1), (369, -1), (370, -1)]
theorem det00Term1Row01_decode : SparsePolynomial.decodeCubic 15 det00Term1Row01 = SparsePolynomial.monoTimes [1] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row01 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term1Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row02 : CoefficientMerge.Poly := [(257, -1), (258, -1), (259, -1), (260, -1), (261, -1), (262, -1), (263, -1), (264, -1), (482, -1), (483, -2), (484, -2), (485, -2), (486, -2), (487, -2), (488, -2), (489, -2), (490, -1), (498, -1), (499, -2), (500, -2), (501, -2), (502, -2), (503, -2), (504, -2), (505, -1), (514, -1), (515, -2), (516, -2), (517, -2), (518, -2), (519, -2), (520, -1), (530, -1), (531, -2), (532, -2), (533, -2), (534, -2), (535, -1), (546, -1), (547, -2), (548, -2), (549, -2), (550, -1), (562, -1), (563, -2), (564, -2), (565, -1), (578, -1), (579, -2), (580, -1), (594, -1), (595, -1)]
theorem det00Term1Row02_decode : SparsePolynomial.decodeCubic 15 det00Term1Row02 = SparsePolynomial.monoTimes [2] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row02 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term1Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row03 : CoefficientMerge.Poly := [(258, -1), (273, -1), (274, -1), (275, -1), (276, -1), (277, -1), (278, -1), (279, -1), (483, -1), (498, -2), (499, -2), (500, -2), (501, -2), (502, -2), (503, -2), (504, -2), (505, -1), (723, -1), (724, -2), (725, -2), (726, -2), (727, -2), (728, -2), (729, -2), (730, -1), (739, -1), (740, -2), (741, -2), (742, -2), (743, -2), (744, -2), (745, -1), (755, -1), (756, -2), (757, -2), (758, -2), (759, -2), (760, -1), (771, -1), (772, -2), (773, -2), (774, -2), (775, -1), (787, -1), (788, -2), (789, -2), (790, -1), (803, -1), (804, -2), (805, -1), (819, -1), (820, -1)]
theorem det00Term1Row03_decode : SparsePolynomial.decodeCubic 15 det00Term1Row03 = SparsePolynomial.monoTimes [3] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row03 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term1Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
