import APPT.Finite15Sparse.Det04Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term2Row04 : CoefficientMerge.Poly := [(35, -1), (50, -1), (65, -1), (80, -1), (81, -1), (82, -1), (83, -1), (84, -1), (260, -1), (275, -1), (290, -1), (305, -1), (306, -1), (307, -1), (308, -1), (309, -1), (485, -1), (500, -2), (515, -2), (530, -2), (531, -2), (532, -2), (533, -2), (534, -2), (535, -1), (536, -1), (537, -1), (725, -1), (740, -2), (755, -2), (756, -2), (757, -2), (758, -2), (759, -2), (760, -1), (761, -1), (762, -1), (965, -1), (980, -2), (981, -2), (982, -2), (983, -2), (984, -2), (985, -1), (986, -1), (987, -1), (1205, -1), (1206, -2), (1207, -2), (1208, -2), (1209, -2), (1210, -1), (1211, -1), (1212, -1), (1221, -1), (1222, -2), (1223, -2), (1224, -2), (1225, -1), (1226, -1), (1227, -1), (1237, -1), (1238, -2), (1239, -2), (1240, -1), (1241, -1), (1242, -1), (1253, -1), (1254, -2), (1255, -1), (1256, -1), (1257, -1), (1269, -1), (1270, -1), (1271, -1), (1272, -1)]
theorem det04Term2Row04_decode : SparsePolynomial.decodeCubic 15 det04Term2Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det04Pair2 := by decide +kernel
theorem eval_det04Term2Row04 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term2Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det04Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term2Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term2Row05 : CoefficientMerge.Poly := [(36, -1), (51, -1), (66, -1), (81, -1), (96, -1), (97, -1), (98, -1), (99, -1), (261, -1), (276, -1), (291, -1), (306, -1), (321, -1), (322, -1), (323, -1), (324, -1), (486, -1), (501, -2), (516, -2), (531, -2), (546, -2), (547, -2), (548, -2), (549, -2), (550, -1), (551, -1), (552, -1), (726, -1), (741, -2), (756, -2), (771, -2), (772, -2), (773, -2), (774, -2), (775, -1), (776, -1), (777, -1), (966, -1), (981, -2), (996, -2), (997, -2), (998, -2), (999, -2), (1000, -1), (1001, -1), (1002, -1), (1206, -1), (1221, -2), (1222, -2), (1223, -2), (1224, -2), (1225, -1), (1226, -1), (1227, -1), (1446, -1), (1447, -2), (1448, -2), (1449, -2), (1450, -1), (1451, -1), (1452, -1), (1462, -1), (1463, -2), (1464, -2), (1465, -1), (1466, -1), (1467, -1), (1478, -1), (1479, -2), (1480, -1), (1481, -1), (1482, -1), (1494, -1), (1495, -1), (1496, -1), (1497, -1)]
theorem det04Term2Row05_decode : SparsePolynomial.decodeCubic 15 det04Term2Row05 = SparsePolynomial.monoTimes [6] (-1 : Int) det04Pair2 := by decide +kernel
theorem eval_det04Term2Row05 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term2Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det04Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term2Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term2Row06 : CoefficientMerge.Poly := [(37, -1), (52, -1), (67, -1), (82, -1), (97, -1), (112, -1), (113, -1), (114, -1), (262, -1), (277, -1), (292, -1), (307, -1), (322, -1), (337, -1), (338, -1), (339, -1), (487, -1), (502, -2), (517, -2), (532, -2), (547, -2), (562, -2), (563, -2), (564, -2), (565, -1), (566, -1), (567, -1), (727, -1), (742, -2), (757, -2), (772, -2), (787, -2), (788, -2), (789, -2), (790, -1), (791, -1), (792, -1), (967, -1), (982, -2), (997, -2), (1012, -2), (1013, -2), (1014, -2), (1015, -1), (1016, -1), (1017, -1), (1207, -1), (1222, -2), (1237, -2), (1238, -2), (1239, -2), (1240, -1), (1241, -1), (1242, -1), (1447, -1), (1462, -2), (1463, -2), (1464, -2), (1465, -1), (1466, -1), (1467, -1), (1687, -1), (1688, -2), (1689, -2), (1690, -1), (1691, -1), (1692, -1), (1703, -1), (1704, -2), (1705, -1), (1706, -1), (1707, -1), (1719, -1), (1720, -1), (1721, -1), (1722, -1)]
theorem det04Term2Row06_decode : SparsePolynomial.decodeCubic 15 det04Term2Row06 = SparsePolynomial.monoTimes [7] (-1 : Int) det04Pair2 := by decide +kernel
theorem eval_det04Term2Row06 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term2Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det04Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term2Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term2Row07 : CoefficientMerge.Poly := [(38, -1), (53, -1), (68, -1), (83, -1), (98, -1), (113, -1), (128, -1), (129, -1), (263, -1), (278, -1), (293, -1), (308, -1), (323, -1), (338, -1), (353, -1), (354, -1), (488, -1), (503, -2), (518, -2), (533, -2), (548, -2), (563, -2), (578, -2), (579, -2), (580, -1), (581, -1), (582, -1), (728, -1), (743, -2), (758, -2), (773, -2), (788, -2), (803, -2), (804, -2), (805, -1), (806, -1), (807, -1), (968, -1), (983, -2), (998, -2), (1013, -2), (1028, -2), (1029, -2), (1030, -1), (1031, -1), (1032, -1), (1208, -1), (1223, -2), (1238, -2), (1253, -2), (1254, -2), (1255, -1), (1256, -1), (1257, -1), (1448, -1), (1463, -2), (1478, -2), (1479, -2), (1480, -1), (1481, -1), (1482, -1), (1688, -1), (1703, -2), (1704, -2), (1705, -1), (1706, -1), (1707, -1), (1928, -1), (1929, -2), (1930, -1), (1931, -1), (1932, -1), (1944, -1), (1945, -1), (1946, -1), (1947, -1)]
theorem det04Term2Row07_decode : SparsePolynomial.decodeCubic 15 det04Term2Row07 = SparsePolynomial.monoTimes [8] (-1 : Int) det04Pair2 := by decide +kernel
theorem eval_det04Term2Row07 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term2Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det04Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term2Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
