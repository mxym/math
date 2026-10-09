import APPT.Finite15Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term3Row08 : CoefficientMerge.Poly := [(372, 2), (373, 2), (374, 2), (597, 2), (598, 2), (599, 2), (822, 2), (823, 2), (824, 2), (1047, 2), (1048, 2), (1049, 2), (1272, 2), (1273, 2), (1274, 2), (1497, 2), (1498, 2), (1499, 2), (1722, 2), (1723, 2), (1724, 2), (1947, 2), (1948, 2), (1949, 2), (2172, 2), (2173, 2), (2174, 2), (2187, 2), (2188, 2), (2189, 2)]
theorem det00Term3Row08_decode : SparsePolynomial.decodeCubic 15 det00Term3Row08 = SparsePolynomial.monoTimes [9] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row08 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term3Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row09 : CoefficientMerge.Poly := [(387, 2), (388, 2), (389, 2), (612, 2), (613, 2), (614, 2), (837, 2), (838, 2), (839, 2), (1062, 2), (1063, 2), (1064, 2), (1287, 2), (1288, 2), (1289, 2), (1512, 2), (1513, 2), (1514, 2), (1737, 2), (1738, 2), (1739, 2), (1962, 2), (1963, 2), (1964, 2), (2187, 2), (2188, 2), (2189, 2), (2412, 2), (2413, 2), (2414, 2)]
theorem det00Term3Row09_decode : SparsePolynomial.decodeCubic 15 det00Term3Row09 = SparsePolynomial.monoTimes [10] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row09 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term3Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [10]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
