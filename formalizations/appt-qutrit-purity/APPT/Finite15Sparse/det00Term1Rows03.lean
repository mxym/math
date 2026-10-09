import APPT.Finite15Sparse.Det00Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term1Row12 : CoefficientMerge.Poly := [(267, -1), (282, -1), (297, -1), (312, -1), (327, -1), (342, -1), (357, -1), (372, -1), (492, -1), (507, -2), (522, -2), (537, -2), (552, -2), (567, -2), (582, -2), (597, -2), (612, -1), (732, -1), (747, -2), (762, -2), (777, -2), (792, -2), (807, -2), (822, -2), (837, -1), (972, -1), (987, -2), (1002, -2), (1017, -2), (1032, -2), (1047, -2), (1062, -1), (1212, -1), (1227, -2), (1242, -2), (1257, -2), (1272, -2), (1287, -1), (1452, -1), (1467, -2), (1482, -2), (1497, -2), (1512, -1), (1692, -1), (1707, -2), (1722, -2), (1737, -1), (1932, -1), (1947, -2), (1962, -1), (2172, -1), (2187, -1)]
theorem det00Term1Row12_decode : SparsePolynomial.decodeCubic 15 det00Term1Row12 = SparsePolynomial.monoTimes [12] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row12 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term1Row12 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [12]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row12_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
