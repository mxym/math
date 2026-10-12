import APPT.Finite9Sparse.Det03Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term2Row04 : CoefficientMerge.Poly := [(nat_lit 23, Int.negSucc (nat_lit 0)), (nat_lit 32, Int.negSucc (nat_lit 0)), (nat_lit 104, Int.negSucc (nat_lit 0)), (nat_lit 113, Int.negSucc (nat_lit 0)), (nat_lit 185, Int.negSucc (nat_lit 0)), (nat_lit 194, Int.negSucc (nat_lit 1)), (nat_lit 203, Int.negSucc (nat_lit 0)), (nat_lit 212, Int.negSucc (nat_lit 0)), (nat_lit 213, Int.negSucc (nat_lit 0)), (nat_lit 275, Int.negSucc (nat_lit 0)), (nat_lit 284, Int.negSucc (nat_lit 0)), (nat_lit 293, Int.negSucc (nat_lit 0)), (nat_lit 294, Int.negSucc (nat_lit 0))]
theorem det03Term2Row04_decode : SparsePolynomial.decodeCubic 9 det03Term2Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det03Pair2 := by decide +kernel
theorem eval_det03Term2Row04 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term2Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term2Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
