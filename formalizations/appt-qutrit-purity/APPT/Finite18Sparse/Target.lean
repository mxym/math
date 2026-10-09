import APPT.Finite18Sparse.targetProductProduct
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def targetCoeffs : CoefficientMerge.Poly := targetProductCoeffs
theorem eval_targetCoeffs (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) targetCoeffs = (26*(total g)^2-400*squareTotal g)*total g := by
  rw [targetCoeffs, eval_targetProductCoeffs, eval_polyTotal, eval_targetQuadratic]
  ring

end APPT.Finite18
