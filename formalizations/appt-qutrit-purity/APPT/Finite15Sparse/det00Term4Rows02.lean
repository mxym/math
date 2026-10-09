import APPT.Finite15Sparse.Det00Pair4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term4Row08 : CoefficientMerge.Poly := [(129, 2), (130, 2), (131, 2), (132, 2), (133, 2), (134, 2), (354, 2), (355, 2), (356, 2), (357, 2), (358, 2), (359, 2), (579, 2), (580, 2), (581, 2), (582, 2), (583, 2), (584, 2), (804, 2), (805, 2), (806, 2), (807, 2), (808, 2), (809, 2), (1029, 2), (1030, 2), (1031, 2), (1032, 2), (1033, 2), (1034, 2), (1254, 2), (1255, 2), (1256, 2), (1257, 2), (1258, 2), (1259, 2), (1479, 2), (1480, 2), (1481, 2), (1482, 2), (1483, 2), (1484, 2), (1704, 2), (1705, 2), (1706, 2), (1707, 2), (1708, 2), (1709, 2), (1929, 2), (1930, 2), (1931, 2), (1932, 2), (1933, 2), (1934, 2), (1944, 2), (1945, 4), (1946, 4), (1947, 4), (1948, 2), (1949, 2), (1960, 2), (1961, 4), (1962, 4), (1963, 2), (1964, 2), (1976, 2), (1977, 4), (1978, 2), (1979, 2), (1992, 2), (1993, 2), (1994, 2)]
theorem det00Term4Row08_decode : SparsePolynomial.decodeCubic 15 det00Term4Row08 = SparsePolynomial.monoTimes [8] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row08 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term4Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term4Row09 : CoefficientMerge.Poly := [(144, 2), (145, 2), (146, 2), (147, 2), (148, 2), (149, 2), (369, 2), (370, 2), (371, 2), (372, 2), (373, 2), (374, 2), (594, 2), (595, 2), (596, 2), (597, 2), (598, 2), (599, 2), (819, 2), (820, 2), (821, 2), (822, 2), (823, 2), (824, 2), (1044, 2), (1045, 2), (1046, 2), (1047, 2), (1048, 2), (1049, 2), (1269, 2), (1270, 2), (1271, 2), (1272, 2), (1273, 2), (1274, 2), (1494, 2), (1495, 2), (1496, 2), (1497, 2), (1498, 2), (1499, 2), (1719, 2), (1720, 2), (1721, 2), (1722, 2), (1723, 2), (1724, 2), (1944, 2), (1945, 2), (1946, 2), (1947, 2), (1948, 2), (1949, 2), (2169, 2), (2170, 4), (2171, 4), (2172, 4), (2173, 2), (2174, 2), (2185, 2), (2186, 4), (2187, 4), (2188, 2), (2189, 2), (2201, 2), (2202, 4), (2203, 2), (2204, 2), (2217, 2), (2218, 2), (2219, 2)]
theorem det00Term4Row09_decode : SparsePolynomial.decodeCubic 15 det00Term4Row09 = SparsePolynomial.monoTimes [9] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row09 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term4Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term4Row10 : CoefficientMerge.Poly := [(145, 2), (160, 2), (161, 2), (162, 2), (163, 2), (164, 2), (370, 2), (385, 2), (386, 2), (387, 2), (388, 2), (389, 2), (595, 2), (610, 2), (611, 2), (612, 2), (613, 2), (614, 2), (820, 2), (835, 2), (836, 2), (837, 2), (838, 2), (839, 2), (1045, 2), (1060, 2), (1061, 2), (1062, 2), (1063, 2), (1064, 2), (1270, 2), (1285, 2), (1286, 2), (1287, 2), (1288, 2), (1289, 2), (1495, 2), (1510, 2), (1511, 2), (1512, 2), (1513, 2), (1514, 2), (1720, 2), (1735, 2), (1736, 2), (1737, 2), (1738, 2), (1739, 2), (1945, 2), (1960, 2), (1961, 2), (1962, 2), (1963, 2), (1964, 2), (2170, 2), (2185, 4), (2186, 4), (2187, 4), (2188, 2), (2189, 2), (2410, 2), (2411, 4), (2412, 4), (2413, 2), (2414, 2), (2426, 2), (2427, 4), (2428, 2), (2429, 2), (2442, 2), (2443, 2), (2444, 2)]
theorem det00Term4Row10_decode : SparsePolynomial.decodeCubic 15 det00Term4Row10 = SparsePolynomial.monoTimes [10] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row10 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term4Row10 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [10]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row10_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term4Row11 : CoefficientMerge.Poly := [(146, 2), (161, 2), (176, 2), (177, 2), (178, 2), (179, 2), (371, 2), (386, 2), (401, 2), (402, 2), (403, 2), (404, 2), (596, 2), (611, 2), (626, 2), (627, 2), (628, 2), (629, 2), (821, 2), (836, 2), (851, 2), (852, 2), (853, 2), (854, 2), (1046, 2), (1061, 2), (1076, 2), (1077, 2), (1078, 2), (1079, 2), (1271, 2), (1286, 2), (1301, 2), (1302, 2), (1303, 2), (1304, 2), (1496, 2), (1511, 2), (1526, 2), (1527, 2), (1528, 2), (1529, 2), (1721, 2), (1736, 2), (1751, 2), (1752, 2), (1753, 2), (1754, 2), (1946, 2), (1961, 2), (1976, 2), (1977, 2), (1978, 2), (1979, 2), (2171, 2), (2186, 4), (2201, 4), (2202, 4), (2203, 2), (2204, 2), (2411, 2), (2426, 4), (2427, 4), (2428, 2), (2429, 2), (2651, 2), (2652, 4), (2653, 2), (2654, 2), (2667, 2), (2668, 2), (2669, 2)]
theorem det00Term4Row11_decode : SparsePolynomial.decodeCubic 15 det00Term4Row11 = SparsePolynomial.monoTimes [11] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row11 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term4Row11 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [11]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row11_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
