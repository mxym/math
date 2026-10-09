import APPT.Finite15Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term3Row08 : CoefficientMerge.Poly := [(371, 2), (372, 2), (373, 2), (374, 2), (596, 2), (597, 2), (598, 2), (599, 2), (821, 2), (822, 2), (823, 2), (824, 2), (1046, 2), (1047, 2), (1048, 2), (1049, 2), (1271, 2), (1272, 2), (1273, 2), (1274, 2), (1496, 2), (1497, 2), (1498, 2), (1499, 2), (1721, 2), (1722, 2), (1723, 2), (1724, 2), (1946, 2), (1947, 2), (1948, 2), (1949, 2), (2171, 2), (2172, 2), (2173, 2), (2174, 2), (2186, 2), (2187, 2), (2188, 2), (2189, 2), (2201, 2), (2202, 2), (2203, 2), (2204, 2)]
theorem det04Term3Row08_decode : SparsePolynomial.decodeCubic 15 det04Term3Row08 = SparsePolynomial.monoTimes [9] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row08 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row09 : CoefficientMerge.Poly := [(386, 2), (387, 2), (388, 2), (389, 2), (611, 2), (612, 2), (613, 2), (614, 2), (836, 2), (837, 2), (838, 2), (839, 2), (1061, 2), (1062, 2), (1063, 2), (1064, 2), (1286, 2), (1287, 2), (1288, 2), (1289, 2), (1511, 2), (1512, 2), (1513, 2), (1514, 2), (1736, 2), (1737, 2), (1738, 2), (1739, 2), (1961, 2), (1962, 2), (1963, 2), (1964, 2), (2186, 2), (2187, 2), (2188, 2), (2189, 2), (2411, 2), (2412, 2), (2413, 2), (2414, 2), (2426, 2), (2427, 2), (2428, 2), (2429, 2)]
theorem det04Term3Row09_decode : SparsePolynomial.decodeCubic 15 det04Term3Row09 = SparsePolynomial.monoTimes [10] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row09 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [10]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row10 : CoefficientMerge.Poly := [(401, 2), (402, 2), (403, 2), (404, 2), (626, 2), (627, 2), (628, 2), (629, 2), (851, 2), (852, 2), (853, 2), (854, 2), (1076, 2), (1077, 2), (1078, 2), (1079, 2), (1301, 2), (1302, 2), (1303, 2), (1304, 2), (1526, 2), (1527, 2), (1528, 2), (1529, 2), (1751, 2), (1752, 2), (1753, 2), (1754, 2), (1976, 2), (1977, 2), (1978, 2), (1979, 2), (2201, 2), (2202, 2), (2203, 2), (2204, 2), (2426, 2), (2427, 2), (2428, 2), (2429, 2), (2651, 2), (2652, 2), (2653, 2), (2654, 2)]
theorem det04Term3Row10_decode : SparsePolynomial.decodeCubic 15 det04Term3Row10 = SparsePolynomial.monoTimes [11] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row10 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term3Row10 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [11]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row10_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
