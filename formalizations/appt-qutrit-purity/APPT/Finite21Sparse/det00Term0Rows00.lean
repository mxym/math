import APPT.Finite21Sparse.Det00Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det00Term0Row00 : CoefficientMerge.Poly := [(7013, 8), (7034, 8), (7055, 8), (7454, 8), (7475, 8), (7496, 8), (7895, 8), (7916, 8), (7937, 8), (8336, 8), (8357, 16), (8378, 16), (8798, 8), (8819, 16), (9260, 8)]
theorem det00Term0Row00_decode : SparsePolynomial.decodeCubic 21 det00Term0Row00 = SparsePolynomial.monoTimes [20] (2 : Int) det00Pair0 := by decide +kernel
theorem eval_det00Term0Row00 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det00Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [20]*SparsePolynomial.eval (gapValues g) det00Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite21
