import APPT.Finite9Sparse.Det03Pair2
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term2Row04 : CoefficientMerge.Poly := [(23, -1), (32, -1), (104, -1), (113, -1), (185, -1), (194, -2), (203, -1), (212, -1), (213, -1), (275, -1), (284, -1), (293, -1), (294, -1)]
theorem det03Term2Row04_decode : SparsePolynomial.decodeCubic 9 det03Term2Row04 = SparsePolynomial.monoTimes [5] (-1 : Int) det03Pair2 := by decide +kernel
theorem eval_det03Term2Row04 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term2Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det03Pair2 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term2Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
