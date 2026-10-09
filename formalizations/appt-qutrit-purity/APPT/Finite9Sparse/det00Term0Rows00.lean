import APPT.Finite9Sparse.Det00Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Term0Row00 : CoefficientMerge.Poly := [(305, 8), (314, 8), (323, 8), (386, 8), (395, 8), (404, 8), (467, 8), (476, 8), (485, 8), (548, 8), (557, 16), (566, 16), (638, 8), (647, 16), (728, 8)]
theorem det00Term0Row00_decode : SparsePolynomial.decodeCubic 9 det00Term0Row00 = SparsePolynomial.monoTimes [8] (2 : Int) det00Pair0 := by decide +kernel
theorem eval_det00Term0Row00 (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [8]*SparsePolynomial.eval (gapValues g) det00Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite9
