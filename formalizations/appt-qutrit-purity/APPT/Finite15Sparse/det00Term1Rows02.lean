import APPT.Finite15Sparse.Det00Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term1Row08 : CoefficientMerge.Poly := [(263, -1), (278, -1), (293, -1), (308, -1), (323, -1), (338, -1), (353, -1), (354, -1), (488, -1), (503, -2), (518, -2), (533, -2), (548, -2), (563, -2), (578, -2), (579, -2), (580, -1), (728, -1), (743, -2), (758, -2), (773, -2), (788, -2), (803, -2), (804, -2), (805, -1), (968, -1), (983, -2), (998, -2), (1013, -2), (1028, -2), (1029, -2), (1030, -1), (1208, -1), (1223, -2), (1238, -2), (1253, -2), (1254, -2), (1255, -1), (1448, -1), (1463, -2), (1478, -2), (1479, -2), (1480, -1), (1688, -1), (1703, -2), (1704, -2), (1705, -1), (1928, -1), (1929, -2), (1930, -1), (1944, -1), (1945, -1)]
theorem det00Term1Row08_decode : SparsePolynomial.decodeCubic 15 det00Term1Row08 = SparsePolynomial.monoTimes [8] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row08 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term1Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row09 : CoefficientMerge.Poly := [(264, -1), (279, -1), (294, -1), (309, -1), (324, -1), (339, -1), (354, -1), (369, -1), (489, -1), (504, -2), (519, -2), (534, -2), (549, -2), (564, -2), (579, -2), (594, -2), (595, -1), (729, -1), (744, -2), (759, -2), (774, -2), (789, -2), (804, -2), (819, -2), (820, -1), (969, -1), (984, -2), (999, -2), (1014, -2), (1029, -2), (1044, -2), (1045, -1), (1209, -1), (1224, -2), (1239, -2), (1254, -2), (1269, -2), (1270, -1), (1449, -1), (1464, -2), (1479, -2), (1494, -2), (1495, -1), (1689, -1), (1704, -2), (1719, -2), (1720, -1), (1929, -1), (1944, -2), (1945, -1), (2169, -1), (2170, -1)]
theorem det00Term1Row09_decode : SparsePolynomial.decodeCubic 15 det00Term1Row09 = SparsePolynomial.monoTimes [9] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row09 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term1Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row10 : CoefficientMerge.Poly := [(265, -1), (280, -1), (295, -1), (310, -1), (325, -1), (340, -1), (355, -1), (370, -1), (490, -1), (505, -2), (520, -2), (535, -2), (550, -2), (565, -2), (580, -2), (595, -2), (610, -1), (730, -1), (745, -2), (760, -2), (775, -2), (790, -2), (805, -2), (820, -2), (835, -1), (970, -1), (985, -2), (1000, -2), (1015, -2), (1030, -2), (1045, -2), (1060, -1), (1210, -1), (1225, -2), (1240, -2), (1255, -2), (1270, -2), (1285, -1), (1450, -1), (1465, -2), (1480, -2), (1495, -2), (1510, -1), (1690, -1), (1705, -2), (1720, -2), (1735, -1), (1930, -1), (1945, -2), (1960, -1), (2170, -1), (2185, -1)]
theorem det00Term1Row10_decode : SparsePolynomial.decodeCubic 15 det00Term1Row10 = SparsePolynomial.monoTimes [10] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row10 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term1Row10 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [10]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row10_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row11 : CoefficientMerge.Poly := [(266, -1), (281, -1), (296, -1), (311, -1), (326, -1), (341, -1), (356, -1), (371, -1), (491, -1), (506, -2), (521, -2), (536, -2), (551, -2), (566, -2), (581, -2), (596, -2), (611, -1), (731, -1), (746, -2), (761, -2), (776, -2), (791, -2), (806, -2), (821, -2), (836, -1), (971, -1), (986, -2), (1001, -2), (1016, -2), (1031, -2), (1046, -2), (1061, -1), (1211, -1), (1226, -2), (1241, -2), (1256, -2), (1271, -2), (1286, -1), (1451, -1), (1466, -2), (1481, -2), (1496, -2), (1511, -1), (1691, -1), (1706, -2), (1721, -2), (1736, -1), (1931, -1), (1946, -2), (1961, -1), (2171, -1), (2186, -1)]
theorem det00Term1Row11_decode : SparsePolynomial.decodeCubic 15 det00Term1Row11 = SparsePolynomial.monoTimes [11] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row11 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term1Row11 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [11]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row11_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
