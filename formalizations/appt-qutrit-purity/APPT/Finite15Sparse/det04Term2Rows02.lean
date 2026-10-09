import APPT.Finite15Sparse.Det04Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term2Row08 : CoefficientMerge.Poly := [(39, -1), (54, -1), (69, -1), (84, -1), (99, -1), (114, -1), (129, -1), (144, -1), (264, -1), (279, -1), (294, -1), (309, -1), (324, -1), (339, -1), (354, -1), (369, -1), (489, -1), (504, -2), (519, -2), (534, -2), (549, -2), (564, -2), (579, -2), (594, -2), (595, -1), (596, -1), (597, -1), (729, -1), (744, -2), (759, -2), (774, -2), (789, -2), (804, -2), (819, -2), (820, -1), (821, -1), (822, -1), (969, -1), (984, -2), (999, -2), (1014, -2), (1029, -2), (1044, -2), (1045, -1), (1046, -1), (1047, -1), (1209, -1), (1224, -2), (1239, -2), (1254, -2), (1269, -2), (1270, -1), (1271, -1), (1272, -1), (1449, -1), (1464, -2), (1479, -2), (1494, -2), (1495, -1), (1496, -1), (1497, -1), (1689, -1), (1704, -2), (1719, -2), (1720, -1), (1721, -1), (1722, -1), (1929, -1), (1944, -2), (1945, -1), (1946, -1), (1947, -1), (2169, -1), (2170, -1), (2171, -1), (2172, -1)]
theorem det04Term2Row08_decode : SparsePolynomial.decodeCubic 15 det04Term2Row08 = SparsePolynomial.monoTimes [9] (-1 : Int) det04Pair2 := by decide +kernel
theorem eval_det04Term2Row08 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term2Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det04Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term2Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term2Row09 : CoefficientMerge.Poly := [(40, -1), (55, -1), (70, -1), (85, -1), (100, -1), (115, -1), (130, -1), (145, -1), (265, -1), (280, -1), (295, -1), (310, -1), (325, -1), (340, -1), (355, -1), (370, -1), (490, -1), (505, -2), (520, -2), (535, -2), (550, -2), (565, -2), (580, -2), (595, -2), (610, -1), (611, -1), (612, -1), (730, -1), (745, -2), (760, -2), (775, -2), (790, -2), (805, -2), (820, -2), (835, -1), (836, -1), (837, -1), (970, -1), (985, -2), (1000, -2), (1015, -2), (1030, -2), (1045, -2), (1060, -1), (1061, -1), (1062, -1), (1210, -1), (1225, -2), (1240, -2), (1255, -2), (1270, -2), (1285, -1), (1286, -1), (1287, -1), (1450, -1), (1465, -2), (1480, -2), (1495, -2), (1510, -1), (1511, -1), (1512, -1), (1690, -1), (1705, -2), (1720, -2), (1735, -1), (1736, -1), (1737, -1), (1930, -1), (1945, -2), (1960, -1), (1961, -1), (1962, -1), (2170, -1), (2185, -1), (2186, -1), (2187, -1)]
theorem det04Term2Row09_decode : SparsePolynomial.decodeCubic 15 det04Term2Row09 = SparsePolynomial.monoTimes [10] (-1 : Int) det04Pair2 := by decide +kernel
theorem eval_det04Term2Row09 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term2Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [10]*SparsePolynomial.eval (gapValues g) det04Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term2Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term2Row10 : CoefficientMerge.Poly := [(41, -1), (56, -1), (71, -1), (86, -1), (101, -1), (116, -1), (131, -1), (146, -1), (266, -1), (281, -1), (296, -1), (311, -1), (326, -1), (341, -1), (356, -1), (371, -1), (491, -1), (506, -2), (521, -2), (536, -2), (551, -2), (566, -2), (581, -2), (596, -2), (611, -1), (626, -1), (627, -1), (731, -1), (746, -2), (761, -2), (776, -2), (791, -2), (806, -2), (821, -2), (836, -1), (851, -1), (852, -1), (971, -1), (986, -2), (1001, -2), (1016, -2), (1031, -2), (1046, -2), (1061, -1), (1076, -1), (1077, -1), (1211, -1), (1226, -2), (1241, -2), (1256, -2), (1271, -2), (1286, -1), (1301, -1), (1302, -1), (1451, -1), (1466, -2), (1481, -2), (1496, -2), (1511, -1), (1526, -1), (1527, -1), (1691, -1), (1706, -2), (1721, -2), (1736, -1), (1751, -1), (1752, -1), (1931, -1), (1946, -2), (1961, -1), (1976, -1), (1977, -1), (2171, -1), (2186, -1), (2201, -1), (2202, -1)]
theorem det04Term2Row10_decode : SparsePolynomial.decodeCubic 15 det04Term2Row10 = SparsePolynomial.monoTimes [11] (-1 : Int) det04Pair2 := by decide +kernel
theorem eval_det04Term2Row10 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term2Row10 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [11]*SparsePolynomial.eval (gapValues g) det04Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term2Row10_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
