import APPT.Finite15Sparse.Det00Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term1Row12 : CoefficientMerge.Poly := [(nat_lit 267, Int.negSucc (nat_lit 0)), (nat_lit 282, Int.negSucc (nat_lit 0)), (nat_lit 297, Int.negSucc (nat_lit 0)), (nat_lit 312, Int.negSucc (nat_lit 0)), (nat_lit 327, Int.negSucc (nat_lit 0)), (nat_lit 342, Int.negSucc (nat_lit 0)), (nat_lit 357, Int.negSucc (nat_lit 0)), (nat_lit 372, Int.negSucc (nat_lit 0)), (nat_lit 492, Int.negSucc (nat_lit 0)), (nat_lit 507, Int.negSucc (nat_lit 1)), (nat_lit 522, Int.negSucc (nat_lit 1)), (nat_lit 537, Int.negSucc (nat_lit 1)), (nat_lit 552, Int.negSucc (nat_lit 1)), (nat_lit 567, Int.negSucc (nat_lit 1)), (nat_lit 582, Int.negSucc (nat_lit 1)), (nat_lit 597, Int.negSucc (nat_lit 1)), (nat_lit 612, Int.negSucc (nat_lit 0)), (nat_lit 732, Int.negSucc (nat_lit 0)), (nat_lit 747, Int.negSucc (nat_lit 1)), (nat_lit 762, Int.negSucc (nat_lit 1)), (nat_lit 777, Int.negSucc (nat_lit 1)), (nat_lit 792, Int.negSucc (nat_lit 1)), (nat_lit 807, Int.negSucc (nat_lit 1)), (nat_lit 822, Int.negSucc (nat_lit 1)), (nat_lit 837, Int.negSucc (nat_lit 0)), (nat_lit 972, Int.negSucc (nat_lit 0)), (nat_lit 987, Int.negSucc (nat_lit 1)), (nat_lit 1002, Int.negSucc (nat_lit 1)), (nat_lit 1017, Int.negSucc (nat_lit 1)), (nat_lit 1032, Int.negSucc (nat_lit 1)), (nat_lit 1047, Int.negSucc (nat_lit 1)), (nat_lit 1062, Int.negSucc (nat_lit 0)), (nat_lit 1212, Int.negSucc (nat_lit 0)), (nat_lit 1227, Int.negSucc (nat_lit 1)), (nat_lit 1242, Int.negSucc (nat_lit 1)), (nat_lit 1257, Int.negSucc (nat_lit 1)), (nat_lit 1272, Int.negSucc (nat_lit 1)), (nat_lit 1287, Int.negSucc (nat_lit 0)), (nat_lit 1452, Int.negSucc (nat_lit 0)), (nat_lit 1467, Int.negSucc (nat_lit 1)), (nat_lit 1482, Int.negSucc (nat_lit 1)), (nat_lit 1497, Int.negSucc (nat_lit 1)), (nat_lit 1512, Int.negSucc (nat_lit 0)), (nat_lit 1692, Int.negSucc (nat_lit 0)), (nat_lit 1707, Int.negSucc (nat_lit 1)), (nat_lit 1722, Int.negSucc (nat_lit 1)), (nat_lit 1737, Int.negSucc (nat_lit 0)), (nat_lit 1932, Int.negSucc (nat_lit 0)), (nat_lit 1947, Int.negSucc (nat_lit 1)), (nat_lit 1962, Int.negSucc (nat_lit 0)), (nat_lit 2172, Int.negSucc (nat_lit 0)), (nat_lit 2187, Int.negSucc (nat_lit 0))]
theorem det00Term1Row12_decode : SparsePolynomial.decodeCubic 15 det00Term1Row12 = SparsePolynomial.monoTimes [12] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row12 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term1Row12 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [12]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row12_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
