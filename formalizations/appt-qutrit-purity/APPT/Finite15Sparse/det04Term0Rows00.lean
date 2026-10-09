import APPT.Finite15Sparse.Det04Pair0
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term0Row00 : CoefficientMerge.Poly := [(2204, 8), (2219, 8), (2234, 8), (2249, 8), (2429, 8), (2444, 8), (2459, 8), (2474, 8), (2654, 8), (2669, 16), (2684, 16), (2699, 16), (2894, 8), (2909, 16), (2924, 16), (3134, 8), (3149, 16), (3374, 8)]
theorem det04Term0Row00_decode : SparsePolynomial.decodeCubic 15 det04Term0Row00 = SparsePolynomial.monoTimes [14] (2 : Int) det04Pair0 := by decide +kernel
theorem eval_det04Term0Row00 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term0Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [14]*SparsePolynomial.eval (gapValues g) det04Pair0 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term0Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
