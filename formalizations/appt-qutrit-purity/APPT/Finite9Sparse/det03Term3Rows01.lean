import APPT.Finite9Sparse.Det03Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term3Row04 : CoefficientMerge.Poly := [(131, 2), (132, 2), (133, 2), (134, 2), (212, 2), (213, 2), (214, 2), (215, 2), (293, 2), (294, 2), (295, 2), (296, 2), (374, 2), (375, 2), (376, 2), (377, 2), (455, 2), (456, 2), (457, 2), (458, 2)]
theorem det03Term3Row04_decode : SparsePolynomial.decodeCubic 9 det03Term3Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row04 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term3Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
