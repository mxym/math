import APPT.Finite21Sparse.Det03Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det03Term3Row00 : CoefficientMerge.Poly := [(479, 2), (480, 2), (481, 2), (482, 2), (500, 2), (501, 2), (502, 2), (503, 2), (521, 2), (522, 2), (523, 2), (524, 2), (542, 2), (543, 2), (544, 2), (545, 2), (563, 2), (564, 2), (565, 2), (566, 2), (584, 2), (585, 2), (586, 2), (587, 2), (605, 2), (606, 2), (607, 2), (608, 2), (626, 2), (627, 2), (628, 2), (629, 2), (647, 2), (648, 2), (649, 2), (650, 2), (668, 2), (669, 2), (670, 2), (671, 2), (689, 2), (690, 2), (691, 2), (692, 2), (710, 2), (711, 2), (712, 2), (713, 2), (731, 2), (732, 2), (733, 2), (734, 2), (752, 2), (753, 2), (754, 2), (755, 2), (773, 2), (774, 2), (775, 2), (776, 2), (794, 2), (795, 2), (796, 2), (797, 2), (815, 2), (816, 2), (817, 2), (818, 2)]
theorem det03Term3Row00_decode : SparsePolynomial.decodeCubic 21 det03Term3Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row00 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row01 : CoefficientMerge.Poly := [(500, 2), (501, 2), (502, 2), (503, 2), (941, 2), (942, 2), (943, 2), (944, 2), (962, 2), (963, 2), (964, 2), (965, 2), (983, 2), (984, 2), (985, 2), (986, 2), (1004, 2), (1005, 2), (1006, 2), (1007, 2), (1025, 2), (1026, 2), (1027, 2), (1028, 2), (1046, 2), (1047, 2), (1048, 2), (1049, 2), (1067, 2), (1068, 2), (1069, 2), (1070, 2), (1088, 2), (1089, 2), (1090, 2), (1091, 2), (1109, 2), (1110, 2), (1111, 2), (1112, 2), (1130, 2), (1131, 2), (1132, 2), (1133, 2), (1151, 2), (1152, 2), (1153, 2), (1154, 2), (1172, 2), (1173, 2), (1174, 2), (1175, 2), (1193, 2), (1194, 2), (1195, 2), (1196, 2), (1214, 2), (1215, 2), (1216, 2), (1217, 2), (1235, 2), (1236, 2), (1237, 2), (1238, 2), (1256, 2), (1257, 2), (1258, 2), (1259, 2)]
theorem det03Term3Row01_decode : SparsePolynomial.decodeCubic 21 det03Term3Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row01 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row02 : CoefficientMerge.Poly := [(521, 2), (522, 2), (523, 2), (524, 2), (962, 2), (963, 2), (964, 2), (965, 2), (1403, 2), (1404, 2), (1405, 2), (1406, 2), (1424, 2), (1425, 2), (1426, 2), (1427, 2), (1445, 2), (1446, 2), (1447, 2), (1448, 2), (1466, 2), (1467, 2), (1468, 2), (1469, 2), (1487, 2), (1488, 2), (1489, 2), (1490, 2), (1508, 2), (1509, 2), (1510, 2), (1511, 2), (1529, 2), (1530, 2), (1531, 2), (1532, 2), (1550, 2), (1551, 2), (1552, 2), (1553, 2), (1571, 2), (1572, 2), (1573, 2), (1574, 2), (1592, 2), (1593, 2), (1594, 2), (1595, 2), (1613, 2), (1614, 2), (1615, 2), (1616, 2), (1634, 2), (1635, 2), (1636, 2), (1637, 2), (1655, 2), (1656, 2), (1657, 2), (1658, 2), (1676, 2), (1677, 2), (1678, 2), (1679, 2), (1697, 2), (1698, 2), (1699, 2), (1700, 2)]
theorem det03Term3Row02_decode : SparsePolynomial.decodeCubic 21 det03Term3Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row02 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term3Row03 : CoefficientMerge.Poly := [(542, 2), (543, 2), (544, 2), (545, 2), (983, 2), (984, 2), (985, 2), (986, 2), (1424, 2), (1425, 2), (1426, 2), (1427, 2), (1865, 2), (1866, 2), (1867, 2), (1868, 2), (1886, 2), (1887, 2), (1888, 2), (1889, 2), (1907, 2), (1908, 2), (1909, 2), (1910, 2), (1928, 2), (1929, 2), (1930, 2), (1931, 2), (1949, 2), (1950, 2), (1951, 2), (1952, 2), (1970, 2), (1971, 2), (1972, 2), (1973, 2), (1991, 2), (1992, 2), (1993, 2), (1994, 2), (2012, 2), (2013, 2), (2014, 2), (2015, 2), (2033, 2), (2034, 2), (2035, 2), (2036, 2), (2054, 2), (2055, 2), (2056, 2), (2057, 2), (2075, 2), (2076, 2), (2077, 2), (2078, 2), (2096, 2), (2097, 2), (2098, 2), (2099, 2), (2117, 2), (2118, 2), (2119, 2), (2120, 2), (2138, 2), (2139, 2), (2140, 2), (2141, 2)]
theorem det03Term3Row03_decode : SparsePolynomial.decodeCubic 21 det03Term3Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row03 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite21
