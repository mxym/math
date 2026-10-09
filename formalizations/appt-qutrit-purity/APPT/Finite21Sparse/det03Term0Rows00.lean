import APPT.Finite21Sparse.Det03Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det03Term0Row00 : CoefficientMerge.Poly := [(6992, 8), (7013, 8), (7034, 8), (7055, 8), (7433, 8), (7454, 8), (7475, 8), (7496, 8), (7874, 8), (7895, 16), (7916, 16), (7937, 16), (8336, 8), (8357, 16), (8378, 16), (8798, 8), (8819, 16), (9260, 8)]
theorem det03Term0Row00_decode : SparsePolynomial.decodeCubic 21 det03Term0Row00 = SparsePolynomial.monoTimes [20] (2 : Int) det03Pair0 := by decide +kernel
theorem eval_det03Term0Row00 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [20]*SparsePolynomial.eval (gapValues g) det03Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite21
