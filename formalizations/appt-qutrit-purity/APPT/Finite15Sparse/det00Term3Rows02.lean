import APPT.Finite15Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term3Row08 : CoefficientMerge.Poly := [(nat_lit 372, Int.ofNat (nat_lit 2)), (nat_lit 373, Int.ofNat (nat_lit 2)), (nat_lit 374, Int.ofNat (nat_lit 2)), (nat_lit 597, Int.ofNat (nat_lit 2)), (nat_lit 598, Int.ofNat (nat_lit 2)), (nat_lit 599, Int.ofNat (nat_lit 2)), (nat_lit 822, Int.ofNat (nat_lit 2)), (nat_lit 823, Int.ofNat (nat_lit 2)), (nat_lit 824, Int.ofNat (nat_lit 2)), (nat_lit 1047, Int.ofNat (nat_lit 2)), (nat_lit 1048, Int.ofNat (nat_lit 2)), (nat_lit 1049, Int.ofNat (nat_lit 2)), (nat_lit 1272, Int.ofNat (nat_lit 2)), (nat_lit 1273, Int.ofNat (nat_lit 2)), (nat_lit 1274, Int.ofNat (nat_lit 2)), (nat_lit 1497, Int.ofNat (nat_lit 2)), (nat_lit 1498, Int.ofNat (nat_lit 2)), (nat_lit 1499, Int.ofNat (nat_lit 2)), (nat_lit 1722, Int.ofNat (nat_lit 2)), (nat_lit 1723, Int.ofNat (nat_lit 2)), (nat_lit 1724, Int.ofNat (nat_lit 2)), (nat_lit 1947, Int.ofNat (nat_lit 2)), (nat_lit 1948, Int.ofNat (nat_lit 2)), (nat_lit 1949, Int.ofNat (nat_lit 2)), (nat_lit 2172, Int.ofNat (nat_lit 2)), (nat_lit 2173, Int.ofNat (nat_lit 2)), (nat_lit 2174, Int.ofNat (nat_lit 2)), (nat_lit 2187, Int.ofNat (nat_lit 2)), (nat_lit 2188, Int.ofNat (nat_lit 2)), (nat_lit 2189, Int.ofNat (nat_lit 2))]
theorem det00Term3Row08_decode : SparsePolynomial.decodeCubic 15 det00Term3Row08 = SparsePolynomial.monoTimes [9] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row08 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term3Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row09 : CoefficientMerge.Poly := [(nat_lit 387, Int.ofNat (nat_lit 2)), (nat_lit 388, Int.ofNat (nat_lit 2)), (nat_lit 389, Int.ofNat (nat_lit 2)), (nat_lit 612, Int.ofNat (nat_lit 2)), (nat_lit 613, Int.ofNat (nat_lit 2)), (nat_lit 614, Int.ofNat (nat_lit 2)), (nat_lit 837, Int.ofNat (nat_lit 2)), (nat_lit 838, Int.ofNat (nat_lit 2)), (nat_lit 839, Int.ofNat (nat_lit 2)), (nat_lit 1062, Int.ofNat (nat_lit 2)), (nat_lit 1063, Int.ofNat (nat_lit 2)), (nat_lit 1064, Int.ofNat (nat_lit 2)), (nat_lit 1287, Int.ofNat (nat_lit 2)), (nat_lit 1288, Int.ofNat (nat_lit 2)), (nat_lit 1289, Int.ofNat (nat_lit 2)), (nat_lit 1512, Int.ofNat (nat_lit 2)), (nat_lit 1513, Int.ofNat (nat_lit 2)), (nat_lit 1514, Int.ofNat (nat_lit 2)), (nat_lit 1737, Int.ofNat (nat_lit 2)), (nat_lit 1738, Int.ofNat (nat_lit 2)), (nat_lit 1739, Int.ofNat (nat_lit 2)), (nat_lit 1962, Int.ofNat (nat_lit 2)), (nat_lit 1963, Int.ofNat (nat_lit 2)), (nat_lit 1964, Int.ofNat (nat_lit 2)), (nat_lit 2187, Int.ofNat (nat_lit 2)), (nat_lit 2188, Int.ofNat (nat_lit 2)), (nat_lit 2189, Int.ofNat (nat_lit 2)), (nat_lit 2412, Int.ofNat (nat_lit 2)), (nat_lit 2413, Int.ofNat (nat_lit 2)), (nat_lit 2414, Int.ofNat (nat_lit 2))]
theorem det00Term3Row09_decode : SparsePolynomial.decodeCubic 15 det00Term3Row09 = SparsePolynomial.monoTimes [10] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row09 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term3Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [10]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
