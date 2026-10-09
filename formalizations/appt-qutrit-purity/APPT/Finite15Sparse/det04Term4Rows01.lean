import APPT.Finite15Sparse.Det04Pair4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term4Row04 : CoefficientMerge.Poly := [(69, 2), (70, 2), (71, 2), (72, 2), (73, 2), (74, 2), (294, 2), (295, 2), (296, 2), (297, 2), (298, 2), (299, 2), (519, 2), (520, 2), (521, 2), (522, 2), (523, 2), (524, 2), (744, 2), (745, 2), (746, 2), (747, 2), (748, 2), (749, 2), (969, 2), (970, 2), (971, 2), (972, 2), (973, 2), (974, 2), (984, 2), (985, 2), (986, 2), (987, 2), (988, 2), (989, 2), (999, 2), (1000, 2), (1001, 2), (1002, 2), (1003, 2), (1004, 2), (1014, 2), (1015, 2), (1016, 2), (1017, 2), (1018, 2), (1019, 2), (1029, 2), (1030, 2), (1031, 2), (1032, 2), (1033, 2), (1034, 2), (1044, 2), (1045, 4), (1046, 4), (1047, 4), (1048, 2), (1049, 2), (1060, 2), (1061, 4), (1062, 4), (1063, 2), (1064, 2), (1076, 2), (1077, 4), (1078, 2), (1079, 2), (1092, 2), (1093, 2), (1094, 2)]
theorem det04Term4Row04_decode : SparsePolynomial.decodeCubic 15 det04Term4Row04 = SparsePolynomial.monoTimes [4] (-1 : Int) det04Pair4 := by decide +kernel
theorem eval_det04Term4Row04 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term4Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det04Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term4Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term4Row05 : CoefficientMerge.Poly := [(84, 2), (85, 2), (86, 2), (87, 2), (88, 2), (89, 2), (309, 2), (310, 2), (311, 2), (312, 2), (313, 2), (314, 2), (534, 2), (535, 2), (536, 2), (537, 2), (538, 2), (539, 2), (759, 2), (760, 2), (761, 2), (762, 2), (763, 2), (764, 2), (984, 2), (985, 2), (986, 2), (987, 2), (988, 2), (989, 2), (1209, 2), (1210, 2), (1211, 2), (1212, 2), (1213, 2), (1214, 2), (1224, 2), (1225, 2), (1226, 2), (1227, 2), (1228, 2), (1229, 2), (1239, 2), (1240, 2), (1241, 2), (1242, 2), (1243, 2), (1244, 2), (1254, 2), (1255, 2), (1256, 2), (1257, 2), (1258, 2), (1259, 2), (1269, 2), (1270, 4), (1271, 4), (1272, 4), (1273, 2), (1274, 2), (1285, 2), (1286, 4), (1287, 4), (1288, 2), (1289, 2), (1301, 2), (1302, 4), (1303, 2), (1304, 2), (1317, 2), (1318, 2), (1319, 2)]
theorem det04Term4Row05_decode : SparsePolynomial.decodeCubic 15 det04Term4Row05 = SparsePolynomial.monoTimes [5] (-1 : Int) det04Pair4 := by decide +kernel
theorem eval_det04Term4Row05 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term4Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det04Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term4Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term4Row06 : CoefficientMerge.Poly := [(99, 2), (100, 2), (101, 2), (102, 2), (103, 2), (104, 2), (324, 2), (325, 2), (326, 2), (327, 2), (328, 2), (329, 2), (549, 2), (550, 2), (551, 2), (552, 2), (553, 2), (554, 2), (774, 2), (775, 2), (776, 2), (777, 2), (778, 2), (779, 2), (999, 2), (1000, 2), (1001, 2), (1002, 2), (1003, 2), (1004, 2), (1224, 2), (1225, 2), (1226, 2), (1227, 2), (1228, 2), (1229, 2), (1449, 2), (1450, 2), (1451, 2), (1452, 2), (1453, 2), (1454, 2), (1464, 2), (1465, 2), (1466, 2), (1467, 2), (1468, 2), (1469, 2), (1479, 2), (1480, 2), (1481, 2), (1482, 2), (1483, 2), (1484, 2), (1494, 2), (1495, 4), (1496, 4), (1497, 4), (1498, 2), (1499, 2), (1510, 2), (1511, 4), (1512, 4), (1513, 2), (1514, 2), (1526, 2), (1527, 4), (1528, 2), (1529, 2), (1542, 2), (1543, 2), (1544, 2)]
theorem det04Term4Row06_decode : SparsePolynomial.decodeCubic 15 det04Term4Row06 = SparsePolynomial.monoTimes [6] (-1 : Int) det04Pair4 := by decide +kernel
theorem eval_det04Term4Row06 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term4Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det04Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term4Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term4Row07 : CoefficientMerge.Poly := [(114, 2), (115, 2), (116, 2), (117, 2), (118, 2), (119, 2), (339, 2), (340, 2), (341, 2), (342, 2), (343, 2), (344, 2), (564, 2), (565, 2), (566, 2), (567, 2), (568, 2), (569, 2), (789, 2), (790, 2), (791, 2), (792, 2), (793, 2), (794, 2), (1014, 2), (1015, 2), (1016, 2), (1017, 2), (1018, 2), (1019, 2), (1239, 2), (1240, 2), (1241, 2), (1242, 2), (1243, 2), (1244, 2), (1464, 2), (1465, 2), (1466, 2), (1467, 2), (1468, 2), (1469, 2), (1689, 2), (1690, 2), (1691, 2), (1692, 2), (1693, 2), (1694, 2), (1704, 2), (1705, 2), (1706, 2), (1707, 2), (1708, 2), (1709, 2), (1719, 2), (1720, 4), (1721, 4), (1722, 4), (1723, 2), (1724, 2), (1735, 2), (1736, 4), (1737, 4), (1738, 2), (1739, 2), (1751, 2), (1752, 4), (1753, 2), (1754, 2), (1767, 2), (1768, 2), (1769, 2)]
theorem det04Term4Row07_decode : SparsePolynomial.decodeCubic 15 det04Term4Row07 = SparsePolynomial.monoTimes [7] (-1 : Int) det04Pair4 := by decide +kernel
theorem eval_det04Term4Row07 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term4Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det04Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term4Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
