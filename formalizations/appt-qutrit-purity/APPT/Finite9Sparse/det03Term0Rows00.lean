import APPT.Finite9Sparse.Det03Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Term0Row00 : CoefficientMerge.Poly := [(296, 8), (305, 8), (314, 8), (323, 8), (377, 8), (386, 8), (395, 8), (404, 8), (458, 8), (467, 16), (476, 16), (485, 16), (548, 8), (557, 16), (566, 16), (638, 8), (647, 16), (728, 8)]
theorem det03Term0Row00_decode : SparsePolynomial.decodeCubic 9 det03Term0Row00 = SparsePolynomial.monoTimes [8] (2 : Int) det03Pair0 := by decide +kernel
theorem eval_det03Term0Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det03Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det03Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
