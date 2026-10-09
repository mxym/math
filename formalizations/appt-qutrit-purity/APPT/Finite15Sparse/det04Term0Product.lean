import APPT.Finite15Sparse.det04Term0Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term0Coeffs : CoefficientMerge.Poly := [(2204, 8), (2219, 8), (2234, 8), (2249, 8), (2429, 8), (2444, 8), (2459, 8), (2474, 8), (2654, 8), (2669, 16), (2684, 16), (2699, 16), (2894, 8), (2909, 16), (2924, 16), (3134, 8), (3149, 16), (3374, 8)]
theorem det04Term0Coeffs_data : det04Term0Coeffs = CoefficientMerge.trim det04Term0Row00 := by decide +kernel
theorem eval_det04Term0Coeffs (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term0Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det04Pair0 := by
  rw [det04Term0Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det04Term0Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det04Pair0 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite15
