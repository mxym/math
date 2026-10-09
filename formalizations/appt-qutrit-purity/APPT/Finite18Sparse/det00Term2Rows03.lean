import APPT.Finite18Sparse.Det00Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det00Term2Row12 : CoefficientMerge.Poly := [(49, -1), (67, -1), (85, -1), (103, -1), (121, -1), (139, -1), (157, -1), (175, -1), (193, -1), (211, -1), (229, -1), (373, -1), (391, -1), (409, -1), (427, -1), (445, -1), (463, -1), (481, -1), (499, -1), (517, -1), (535, -1), (553, -1), (697, -1), (715, -2), (733, -2), (751, -2), (769, -2), (787, -2), (805, -2), (823, -2), (841, -2), (859, -2), (877, -2), (895, -1), (896, -1), (897, -1), (1039, -1), (1057, -2), (1075, -2), (1093, -2), (1111, -2), (1129, -2), (1147, -2), (1165, -2), (1183, -2), (1201, -2), (1219, -1), (1220, -1), (1221, -1), (1381, -1), (1399, -2), (1417, -2), (1435, -2), (1453, -2), (1471, -2), (1489, -2), (1507, -2), (1525, -2), (1543, -1), (1544, -1), (1545, -1), (1723, -1), (1741, -2), (1759, -2), (1777, -2), (1795, -2), (1813, -2), (1831, -2), (1849, -2), (1867, -1), (1868, -1), (1869, -1), (2065, -1), (2083, -2), (2101, -2), (2119, -2), (2137, -2), (2155, -2), (2173, -2), (2191, -1), (2192, -1), (2193, -1), (2407, -1), (2425, -2), (2443, -2), (2461, -2), (2479, -2), (2497, -2), (2515, -1), (2516, -1), (2517, -1), (2749, -1), (2767, -2), (2785, -2), (2803, -2), (2821, -2), (2839, -1), (2840, -1), (2841, -1), (3091, -1), (3109, -2), (3127, -2), (3145, -2), (3163, -1), (3164, -1), (3165, -1), (3433, -1), (3451, -2), (3469, -2), (3487, -1), (3488, -1), (3489, -1), (3775, -1), (3793, -2), (3811, -1), (3812, -1), (3813, -1), (4117, -1), (4135, -1), (4136, -1), (4137, -1)]
theorem det00Term2Row12_decode : SparsePolynomial.decodeCubic 18 det00Term2Row12 = SparsePolynomial.monoTimes [13] (-1 : Int) det00Pair2 := by decide +kernel
theorem eval_det00Term2Row12 (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det00Term2Row12 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [13]*SparsePolynomial.eval (gapValues g) det00Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term2Row12_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite18
