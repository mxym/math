import APPT.Finite15Sparse.Det04Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term1Row04 : CoefficientMerge.Poly := [(259, -1), (274, -1), (289, -1), (290, -1), (291, -1), (292, -1), (293, -1), (294, -1), (484, -1), (499, -2), (514, -2), (515, -2), (516, -2), (517, -2), (518, -2), (519, -2), (520, -1), (521, -1), (724, -1), (739, -2), (740, -2), (741, -2), (742, -2), (743, -2), (744, -2), (745, -1), (746, -1), (964, -1), (965, -2), (966, -2), (967, -2), (968, -2), (969, -2), (970, -1), (971, -1), (980, -1), (981, -2), (982, -2), (983, -2), (984, -2), (985, -1), (986, -1), (996, -1), (997, -2), (998, -2), (999, -2), (1000, -1), (1001, -1), (1012, -1), (1013, -2), (1014, -2), (1015, -1), (1016, -1), (1028, -1), (1029, -2), (1030, -1), (1031, -1), (1044, -1), (1045, -1), (1046, -1)]
theorem det04Term1Row04_decode : SparsePolynomial.decodeCubic 15 det04Term1Row04 = SparsePolynomial.monoTimes [4] (-1 : Int) det04Pair1 := by decide +kernel
theorem eval_det04Term1Row04 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term1Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det04Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term1Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term1Row05 : CoefficientMerge.Poly := [(260, -1), (275, -1), (290, -1), (305, -1), (306, -1), (307, -1), (308, -1), (309, -1), (485, -1), (500, -2), (515, -2), (530, -2), (531, -2), (532, -2), (533, -2), (534, -2), (535, -1), (536, -1), (725, -1), (740, -2), (755, -2), (756, -2), (757, -2), (758, -2), (759, -2), (760, -1), (761, -1), (965, -1), (980, -2), (981, -2), (982, -2), (983, -2), (984, -2), (985, -1), (986, -1), (1205, -1), (1206, -2), (1207, -2), (1208, -2), (1209, -2), (1210, -1), (1211, -1), (1221, -1), (1222, -2), (1223, -2), (1224, -2), (1225, -1), (1226, -1), (1237, -1), (1238, -2), (1239, -2), (1240, -1), (1241, -1), (1253, -1), (1254, -2), (1255, -1), (1256, -1), (1269, -1), (1270, -1), (1271, -1)]
theorem det04Term1Row05_decode : SparsePolynomial.decodeCubic 15 det04Term1Row05 = SparsePolynomial.monoTimes [5] (-1 : Int) det04Pair1 := by decide +kernel
theorem eval_det04Term1Row05 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term1Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det04Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term1Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term1Row06 : CoefficientMerge.Poly := [(261, -1), (276, -1), (291, -1), (306, -1), (321, -1), (322, -1), (323, -1), (324, -1), (486, -1), (501, -2), (516, -2), (531, -2), (546, -2), (547, -2), (548, -2), (549, -2), (550, -1), (551, -1), (726, -1), (741, -2), (756, -2), (771, -2), (772, -2), (773, -2), (774, -2), (775, -1), (776, -1), (966, -1), (981, -2), (996, -2), (997, -2), (998, -2), (999, -2), (1000, -1), (1001, -1), (1206, -1), (1221, -2), (1222, -2), (1223, -2), (1224, -2), (1225, -1), (1226, -1), (1446, -1), (1447, -2), (1448, -2), (1449, -2), (1450, -1), (1451, -1), (1462, -1), (1463, -2), (1464, -2), (1465, -1), (1466, -1), (1478, -1), (1479, -2), (1480, -1), (1481, -1), (1494, -1), (1495, -1), (1496, -1)]
theorem det04Term1Row06_decode : SparsePolynomial.decodeCubic 15 det04Term1Row06 = SparsePolynomial.monoTimes [6] (-1 : Int) det04Pair1 := by decide +kernel
theorem eval_det04Term1Row06 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term1Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det04Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term1Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term1Row07 : CoefficientMerge.Poly := [(262, -1), (277, -1), (292, -1), (307, -1), (322, -1), (337, -1), (338, -1), (339, -1), (487, -1), (502, -2), (517, -2), (532, -2), (547, -2), (562, -2), (563, -2), (564, -2), (565, -1), (566, -1), (727, -1), (742, -2), (757, -2), (772, -2), (787, -2), (788, -2), (789, -2), (790, -1), (791, -1), (967, -1), (982, -2), (997, -2), (1012, -2), (1013, -2), (1014, -2), (1015, -1), (1016, -1), (1207, -1), (1222, -2), (1237, -2), (1238, -2), (1239, -2), (1240, -1), (1241, -1), (1447, -1), (1462, -2), (1463, -2), (1464, -2), (1465, -1), (1466, -1), (1687, -1), (1688, -2), (1689, -2), (1690, -1), (1691, -1), (1703, -1), (1704, -2), (1705, -1), (1706, -1), (1719, -1), (1720, -1), (1721, -1)]
theorem det04Term1Row07_decode : SparsePolynomial.decodeCubic 15 det04Term1Row07 = SparsePolynomial.monoTimes [7] (-1 : Int) det04Pair1 := by decide +kernel
theorem eval_det04Term1Row07 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term1Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det04Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term1Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
