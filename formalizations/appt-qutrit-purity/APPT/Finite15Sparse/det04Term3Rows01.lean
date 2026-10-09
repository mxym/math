import APPT.Finite15Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term3Row04 : CoefficientMerge.Poly := [(311, 2), (312, 2), (313, 2), (314, 2), (536, 2), (537, 2), (538, 2), (539, 2), (761, 2), (762, 2), (763, 2), (764, 2), (986, 2), (987, 2), (988, 2), (989, 2), (1211, 2), (1212, 2), (1213, 2), (1214, 2), (1226, 2), (1227, 2), (1228, 2), (1229, 2), (1241, 2), (1242, 2), (1243, 2), (1244, 2), (1256, 2), (1257, 2), (1258, 2), (1259, 2), (1271, 2), (1272, 2), (1273, 2), (1274, 2), (1286, 2), (1287, 2), (1288, 2), (1289, 2), (1301, 2), (1302, 2), (1303, 2), (1304, 2)]
theorem det04Term3Row04_decode : SparsePolynomial.decodeCubic 15 det04Term3Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row04 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row05 : CoefficientMerge.Poly := [(326, 2), (327, 2), (328, 2), (329, 2), (551, 2), (552, 2), (553, 2), (554, 2), (776, 2), (777, 2), (778, 2), (779, 2), (1001, 2), (1002, 2), (1003, 2), (1004, 2), (1226, 2), (1227, 2), (1228, 2), (1229, 2), (1451, 2), (1452, 2), (1453, 2), (1454, 2), (1466, 2), (1467, 2), (1468, 2), (1469, 2), (1481, 2), (1482, 2), (1483, 2), (1484, 2), (1496, 2), (1497, 2), (1498, 2), (1499, 2), (1511, 2), (1512, 2), (1513, 2), (1514, 2), (1526, 2), (1527, 2), (1528, 2), (1529, 2)]
theorem det04Term3Row05_decode : SparsePolynomial.decodeCubic 15 det04Term3Row05 = SparsePolynomial.monoTimes [6] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row05 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row06 : CoefficientMerge.Poly := [(341, 2), (342, 2), (343, 2), (344, 2), (566, 2), (567, 2), (568, 2), (569, 2), (791, 2), (792, 2), (793, 2), (794, 2), (1016, 2), (1017, 2), (1018, 2), (1019, 2), (1241, 2), (1242, 2), (1243, 2), (1244, 2), (1466, 2), (1467, 2), (1468, 2), (1469, 2), (1691, 2), (1692, 2), (1693, 2), (1694, 2), (1706, 2), (1707, 2), (1708, 2), (1709, 2), (1721, 2), (1722, 2), (1723, 2), (1724, 2), (1736, 2), (1737, 2), (1738, 2), (1739, 2), (1751, 2), (1752, 2), (1753, 2), (1754, 2)]
theorem det04Term3Row06_decode : SparsePolynomial.decodeCubic 15 det04Term3Row06 = SparsePolynomial.monoTimes [7] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row06 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row07 : CoefficientMerge.Poly := [(356, 2), (357, 2), (358, 2), (359, 2), (581, 2), (582, 2), (583, 2), (584, 2), (806, 2), (807, 2), (808, 2), (809, 2), (1031, 2), (1032, 2), (1033, 2), (1034, 2), (1256, 2), (1257, 2), (1258, 2), (1259, 2), (1481, 2), (1482, 2), (1483, 2), (1484, 2), (1706, 2), (1707, 2), (1708, 2), (1709, 2), (1931, 2), (1932, 2), (1933, 2), (1934, 2), (1946, 2), (1947, 2), (1948, 2), (1949, 2), (1961, 2), (1962, 2), (1963, 2), (1964, 2), (1976, 2), (1977, 2), (1978, 2), (1979, 2)]
theorem det04Term3Row07_decode : SparsePolynomial.decodeCubic 15 det04Term3Row07 = SparsePolynomial.monoTimes [8] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row07 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
