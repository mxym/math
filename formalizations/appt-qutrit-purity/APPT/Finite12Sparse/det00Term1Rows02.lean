import APPT.Finite12Sparse.Det00Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term1Row08 : CoefficientMerge.Poly := [(nat_lit 176, Int.negSucc (nat_lit 0)), (nat_lit 188, Int.negSucc (nat_lit 0)), (nat_lit 200, Int.negSucc (nat_lit 0)), (nat_lit 212, Int.negSucc (nat_lit 0)), (nat_lit 224, Int.negSucc (nat_lit 0)), (nat_lit 320, Int.negSucc (nat_lit 0)), (nat_lit 332, Int.negSucc (nat_lit 1)), (nat_lit 344, Int.negSucc (nat_lit 1)), (nat_lit 356, Int.negSucc (nat_lit 1)), (nat_lit 368, Int.negSucc (nat_lit 1)), (nat_lit 380, Int.negSucc (nat_lit 0)), (nat_lit 476, Int.negSucc (nat_lit 0)), (nat_lit 488, Int.negSucc (nat_lit 1)), (nat_lit 500, Int.negSucc (nat_lit 1)), (nat_lit 512, Int.negSucc (nat_lit 1)), (nat_lit 524, Int.negSucc (nat_lit 0)), (nat_lit 632, Int.negSucc (nat_lit 0)), (nat_lit 644, Int.negSucc (nat_lit 1)), (nat_lit 656, Int.negSucc (nat_lit 1)), (nat_lit 668, Int.negSucc (nat_lit 0)), (nat_lit 788, Int.negSucc (nat_lit 0)), (nat_lit 800, Int.negSucc (nat_lit 1)), (nat_lit 812, Int.negSucc (nat_lit 0)), (nat_lit 944, Int.negSucc (nat_lit 0)), (nat_lit 956, Int.negSucc (nat_lit 0))]
theorem det00Term1Row08_decode : SparsePolynomial.decodeCubic 12 det00Term1Row08 = SparsePolynomial.monoTimes [8] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row08 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row09 : CoefficientMerge.Poly := [(nat_lit 177, Int.negSucc (nat_lit 0)), (nat_lit 189, Int.negSucc (nat_lit 0)), (nat_lit 201, Int.negSucc (nat_lit 0)), (nat_lit 213, Int.negSucc (nat_lit 0)), (nat_lit 225, Int.negSucc (nat_lit 0)), (nat_lit 321, Int.negSucc (nat_lit 0)), (nat_lit 333, Int.negSucc (nat_lit 1)), (nat_lit 345, Int.negSucc (nat_lit 1)), (nat_lit 357, Int.negSucc (nat_lit 1)), (nat_lit 369, Int.negSucc (nat_lit 1)), (nat_lit 381, Int.negSucc (nat_lit 0)), (nat_lit 477, Int.negSucc (nat_lit 0)), (nat_lit 489, Int.negSucc (nat_lit 1)), (nat_lit 501, Int.negSucc (nat_lit 1)), (nat_lit 513, Int.negSucc (nat_lit 1)), (nat_lit 525, Int.negSucc (nat_lit 0)), (nat_lit 633, Int.negSucc (nat_lit 0)), (nat_lit 645, Int.negSucc (nat_lit 1)), (nat_lit 657, Int.negSucc (nat_lit 1)), (nat_lit 669, Int.negSucc (nat_lit 0)), (nat_lit 789, Int.negSucc (nat_lit 0)), (nat_lit 801, Int.negSucc (nat_lit 1)), (nat_lit 813, Int.negSucc (nat_lit 0)), (nat_lit 945, Int.negSucc (nat_lit 0)), (nat_lit 957, Int.negSucc (nat_lit 0))]
theorem det00Term1Row09_decode : SparsePolynomial.decodeCubic 12 det00Term1Row09 = SparsePolynomial.monoTimes [9] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row09 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
