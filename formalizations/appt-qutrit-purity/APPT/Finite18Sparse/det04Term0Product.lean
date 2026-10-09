import APPT.Finite18Sparse.det04Term0Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det04Term0Coeffs : CoefficientMerge.Poly := [(4157, 8), (4175, 8), (4193, 8), (4211, 8), (4481, 8), (4499, 8), (4517, 8), (4535, 8), (4805, 8), (4823, 16), (4841, 16), (4859, 16), (5147, 8), (5165, 16), (5183, 16), (5489, 8), (5507, 16), (5831, 8)]
theorem det04Term0Coeffs_data : det04Term0Coeffs = CoefficientMerge.trim det04Term0Row00 := by decide +kernel
theorem eval_det04Term0Coeffs (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term0Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det04Pair0 := by
  rw [det04Term0Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det04Term0Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det04Pair0 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite18
