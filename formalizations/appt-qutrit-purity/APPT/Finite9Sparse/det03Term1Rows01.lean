import APPT.Finite9Sparse.Det03Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term1Row04 : CoefficientMerge.Poly := [(nat_lit 103, Int.negSucc (nat_lit 0)), (nat_lit 112, Int.negSucc (nat_lit 0)), (nat_lit 184, Int.negSucc (nat_lit 0)), (nat_lit 193, Int.negSucc (nat_lit 1)), (nat_lit 202, Int.negSucc (nat_lit 0)), (nat_lit 203, Int.negSucc (nat_lit 0)), (nat_lit 274, Int.negSucc (nat_lit 0)), (nat_lit 283, Int.negSucc (nat_lit 0)), (nat_lit 284, Int.negSucc (nat_lit 0))]
theorem det03Term1Row04_decode : SparsePolynomial.decodeCubic 9 det03Term1Row04 = SparsePolynomial.monoTimes [4] (-1 : Int) det03Pair1 := by decide +kernel
theorem eval_det03Term1Row04 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term1Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term1Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term1Row05 : CoefficientMerge.Poly := [(nat_lit 104, Int.negSucc (nat_lit 0)), (nat_lit 113, Int.negSucc (nat_lit 0)), (nat_lit 185, Int.negSucc (nat_lit 0)), (nat_lit 194, Int.negSucc (nat_lit 1)), (nat_lit 203, Int.negSucc (nat_lit 0)), (nat_lit 212, Int.negSucc (nat_lit 0)), (nat_lit 275, Int.negSucc (nat_lit 0)), (nat_lit 284, Int.negSucc (nat_lit 0)), (nat_lit 293, Int.negSucc (nat_lit 0))]
theorem det03Term1Row05_decode : SparsePolynomial.decodeCubic 9 det03Term1Row05 = SparsePolynomial.monoTimes [5] (-1 : Int) det03Pair1 := by decide +kernel
theorem eval_det03Term1Row05 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term1Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term1Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det03Term1Row06 : CoefficientMerge.Poly := [(nat_lit 105, Int.negSucc (nat_lit 0)), (nat_lit 114, Int.negSucc (nat_lit 0)), (nat_lit 186, Int.negSucc (nat_lit 0)), (nat_lit 195, Int.negSucc (nat_lit 1)), (nat_lit 204, Int.negSucc (nat_lit 0)), (nat_lit 213, Int.negSucc (nat_lit 0)), (nat_lit 276, Int.negSucc (nat_lit 0)), (nat_lit 285, Int.negSucc (nat_lit 0)), (nat_lit 294, Int.negSucc (nat_lit 0))]
theorem det03Term1Row06_decode : SparsePolynomial.decodeCubic 9 det03Term1Row06 = SparsePolynomial.monoTimes [6] (-1 : Int) det03Pair1 := by decide +kernel
theorem eval_det03Term1Row06 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term1Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det03Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term1Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
