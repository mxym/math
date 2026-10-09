import APPT.Finite15Sparse.Det00Pair4
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term4Row12 : CoefficientMerge.Poly := [(147, 2), (162, 2), (177, 2), (192, 2), (193, 2), (194, 2), (372, 2), (387, 2), (402, 2), (417, 2), (418, 2), (419, 2), (597, 2), (612, 2), (627, 2), (642, 2), (643, 2), (644, 2), (822, 2), (837, 2), (852, 2), (867, 2), (868, 2), (869, 2), (1047, 2), (1062, 2), (1077, 2), (1092, 2), (1093, 2), (1094, 2), (1272, 2), (1287, 2), (1302, 2), (1317, 2), (1318, 2), (1319, 2), (1497, 2), (1512, 2), (1527, 2), (1542, 2), (1543, 2), (1544, 2), (1722, 2), (1737, 2), (1752, 2), (1767, 2), (1768, 2), (1769, 2), (1947, 2), (1962, 2), (1977, 2), (1992, 2), (1993, 2), (1994, 2), (2172, 2), (2187, 4), (2202, 4), (2217, 4), (2218, 2), (2219, 2), (2412, 2), (2427, 4), (2442, 4), (2443, 2), (2444, 2), (2652, 2), (2667, 4), (2668, 2), (2669, 2), (2892, 2), (2893, 2), (2894, 2)]
theorem det00Term4Row12_decode : SparsePolynomial.decodeCubic 15 det00Term4Row12 = SparsePolynomial.monoTimes [12] (-1 : Int) det00Pair4 := by decide +kernel
theorem eval_det00Term4Row12 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term4Row12 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [12]*SparsePolynomial.eval (gapValues g) det00Pair4 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term4Row12_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
