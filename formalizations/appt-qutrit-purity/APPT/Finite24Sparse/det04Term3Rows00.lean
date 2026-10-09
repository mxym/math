import APPT.Finite24Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Term3Row00 : CoefficientMerge.Poly := [(620, 2), (621, 2), (622, 2), (623, 2), (644, 2), (645, 2), (646, 2), (647, 2), (668, 2), (669, 2), (670, 2), (671, 2), (692, 2), (693, 2), (694, 2), (695, 2), (716, 2), (717, 2), (718, 2), (719, 2), (740, 2), (741, 2), (742, 2), (743, 2), (764, 2), (765, 2), (766, 2), (767, 2), (788, 2), (789, 2), (790, 2), (791, 2), (812, 2), (813, 2), (814, 2), (815, 2), (836, 2), (837, 2), (838, 2), (839, 2), (860, 2), (861, 2), (862, 2), (863, 2), (884, 2), (885, 2), (886, 2), (887, 2), (908, 2), (909, 2), (910, 2), (911, 2), (932, 2), (933, 2), (934, 2), (935, 2), (956, 2), (957, 2), (958, 2), (959, 2), (980, 2), (981, 2), (982, 2), (983, 2), (1004, 2), (1005, 2), (1006, 2), (1007, 2), (1028, 2), (1029, 2), (1030, 2), (1031, 2), (1052, 2), (1053, 2), (1054, 2), (1055, 2), (1076, 2), (1077, 2), (1078, 2), (1079, 2)]
theorem det04Term3Row00_decode : SparsePolynomial.decodeCubic 24 det04Term3Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row00 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row01 : CoefficientMerge.Poly := [(644, 2), (645, 2), (646, 2), (647, 2), (1220, 2), (1221, 2), (1222, 2), (1223, 2), (1244, 2), (1245, 2), (1246, 2), (1247, 2), (1268, 2), (1269, 2), (1270, 2), (1271, 2), (1292, 2), (1293, 2), (1294, 2), (1295, 2), (1316, 2), (1317, 2), (1318, 2), (1319, 2), (1340, 2), (1341, 2), (1342, 2), (1343, 2), (1364, 2), (1365, 2), (1366, 2), (1367, 2), (1388, 2), (1389, 2), (1390, 2), (1391, 2), (1412, 2), (1413, 2), (1414, 2), (1415, 2), (1436, 2), (1437, 2), (1438, 2), (1439, 2), (1460, 2), (1461, 2), (1462, 2), (1463, 2), (1484, 2), (1485, 2), (1486, 2), (1487, 2), (1508, 2), (1509, 2), (1510, 2), (1511, 2), (1532, 2), (1533, 2), (1534, 2), (1535, 2), (1556, 2), (1557, 2), (1558, 2), (1559, 2), (1580, 2), (1581, 2), (1582, 2), (1583, 2), (1604, 2), (1605, 2), (1606, 2), (1607, 2), (1628, 2), (1629, 2), (1630, 2), (1631, 2), (1652, 2), (1653, 2), (1654, 2), (1655, 2)]
theorem det04Term3Row01_decode : SparsePolynomial.decodeCubic 24 det04Term3Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row01 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row02 : CoefficientMerge.Poly := [(668, 2), (669, 2), (670, 2), (671, 2), (1244, 2), (1245, 2), (1246, 2), (1247, 2), (1820, 2), (1821, 2), (1822, 2), (1823, 2), (1844, 2), (1845, 2), (1846, 2), (1847, 2), (1868, 2), (1869, 2), (1870, 2), (1871, 2), (1892, 2), (1893, 2), (1894, 2), (1895, 2), (1916, 2), (1917, 2), (1918, 2), (1919, 2), (1940, 2), (1941, 2), (1942, 2), (1943, 2), (1964, 2), (1965, 2), (1966, 2), (1967, 2), (1988, 2), (1989, 2), (1990, 2), (1991, 2), (2012, 2), (2013, 2), (2014, 2), (2015, 2), (2036, 2), (2037, 2), (2038, 2), (2039, 2), (2060, 2), (2061, 2), (2062, 2), (2063, 2), (2084, 2), (2085, 2), (2086, 2), (2087, 2), (2108, 2), (2109, 2), (2110, 2), (2111, 2), (2132, 2), (2133, 2), (2134, 2), (2135, 2), (2156, 2), (2157, 2), (2158, 2), (2159, 2), (2180, 2), (2181, 2), (2182, 2), (2183, 2), (2204, 2), (2205, 2), (2206, 2), (2207, 2), (2228, 2), (2229, 2), (2230, 2), (2231, 2)]
theorem det04Term3Row02_decode : SparsePolynomial.decodeCubic 24 det04Term3Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row02 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row03 : CoefficientMerge.Poly := [(692, 2), (693, 2), (694, 2), (695, 2), (1268, 2), (1269, 2), (1270, 2), (1271, 2), (1844, 2), (1845, 2), (1846, 2), (1847, 2), (2420, 2), (2421, 2), (2422, 2), (2423, 2), (2444, 2), (2445, 2), (2446, 2), (2447, 2), (2468, 2), (2469, 2), (2470, 2), (2471, 2), (2492, 2), (2493, 2), (2494, 2), (2495, 2), (2516, 2), (2517, 2), (2518, 2), (2519, 2), (2540, 2), (2541, 2), (2542, 2), (2543, 2), (2564, 2), (2565, 2), (2566, 2), (2567, 2), (2588, 2), (2589, 2), (2590, 2), (2591, 2), (2612, 2), (2613, 2), (2614, 2), (2615, 2), (2636, 2), (2637, 2), (2638, 2), (2639, 2), (2660, 2), (2661, 2), (2662, 2), (2663, 2), (2684, 2), (2685, 2), (2686, 2), (2687, 2), (2708, 2), (2709, 2), (2710, 2), (2711, 2), (2732, 2), (2733, 2), (2734, 2), (2735, 2), (2756, 2), (2757, 2), (2758, 2), (2759, 2), (2780, 2), (2781, 2), (2782, 2), (2783, 2), (2804, 2), (2805, 2), (2806, 2), (2807, 2)]
theorem det04Term3Row03_decode : SparsePolynomial.decodeCubic 24 det04Term3Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row03 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite24
