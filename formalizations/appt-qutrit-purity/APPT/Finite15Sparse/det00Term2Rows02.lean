import APPT.Finite15Sparse.Det00Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term2Row08 : CoefficientMerge.Poly := [(39, -1), (54, -1), (69, -1), (84, -1), (99, -1), (114, -1), (129, -1), (144, -1), (264, -1), (279, -1), (294, -1), (309, -1), (324, -1), (339, -1), (354, -1), (369, -1), (489, -1), (504, -2), (519, -2), (534, -2), (549, -2), (564, -2), (579, -2), (594, -2), (595, -1), (596, -1), (597, -1), (729, -1), (744, -2), (759, -2), (774, -2), (789, -2), (804, -2), (819, -2), (820, -1), (821, -1), (822, -1), (969, -1), (984, -2), (999, -2), (1014, -2), (1029, -2), (1044, -2), (1045, -1), (1046, -1), (1047, -1), (1209, -1), (1224, -2), (1239, -2), (1254, -2), (1269, -2), (1270, -1), (1271, -1), (1272, -1), (1449, -1), (1464, -2), (1479, -2), (1494, -2), (1495, -1), (1496, -1), (1497, -1), (1689, -1), (1704, -2), (1719, -2), (1720, -1), (1721, -1), (1722, -1), (1929, -1), (1944, -2), (1945, -1), (1946, -1), (1947, -1), (2169, -1), (2170, -1), (2171, -1), (2172, -1)]
theorem det00Term2Row08_decode : SparsePolynomial.decodeCubic 15 det00Term2Row08 = SparsePolynomial.monoTimes [9] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row08 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term2Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term2Row09 : CoefficientMerge.Poly := [(40, -1), (55, -1), (70, -1), (85, -1), (100, -1), (115, -1), (130, -1), (145, -1), (265, -1), (280, -1), (295, -1), (310, -1), (325, -1), (340, -1), (355, -1), (370, -1), (490, -1), (505, -2), (520, -2), (535, -2), (550, -2), (565, -2), (580, -2), (595, -2), (610, -1), (611, -1), (612, -1), (730, -1), (745, -2), (760, -2), (775, -2), (790, -2), (805, -2), (820, -2), (835, -1), (836, -1), (837, -1), (970, -1), (985, -2), (1000, -2), (1015, -2), (1030, -2), (1045, -2), (1060, -1), (1061, -1), (1062, -1), (1210, -1), (1225, -2), (1240, -2), (1255, -2), (1270, -2), (1285, -1), (1286, -1), (1287, -1), (1450, -1), (1465, -2), (1480, -2), (1495, -2), (1510, -1), (1511, -1), (1512, -1), (1690, -1), (1705, -2), (1720, -2), (1735, -1), (1736, -1), (1737, -1), (1930, -1), (1945, -2), (1960, -1), (1961, -1), (1962, -1), (2170, -1), (2185, -1), (2186, -1), (2187, -1)]
theorem det00Term2Row09_decode : SparsePolynomial.decodeCubic 15 det00Term2Row09 = SparsePolynomial.monoTimes [10] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row09 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term2Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [10]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
