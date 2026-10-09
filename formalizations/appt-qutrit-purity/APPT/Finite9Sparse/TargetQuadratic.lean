import APPT.Finite9Sparse.Moments
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def targetQuadratic : SparsePolynomial.Poly := [([0,0], -104), ([0,1], -174), ([0,2], -140), ([0,3], -106), ([0,4], -72), ([0,5], -38), ([0,6], -4), ([0,7], 30), ([0,8], 64), ([1,1], -174), ([1,2], -280), ([1,3], -212), ([1,4], -144), ([1,5], -76), ([1,6], -8), ([1,7], 60), ([1,8], 128), ([2,2], -210), ([2,3], -318), ([2,4], -216), ([2,5], -114), ([2,6], -12), ([2,7], 90), ([2,8], 192), ([3,3], -212), ([3,4], -288), ([3,5], -152), ([3,6], -16), ([3,7], 120), ([3,8], 256), ([4,4], -180), ([4,5], -190), ([4,6], -20), ([4,7], 150), ([4,8], 320), ([5,5], -114), ([5,6], -24), ([5,7], 180), ([5,8], 384), ([6,6], -14), ([6,7], 210), ([6,8], 448), ([7,7], 120), ([7,8], 512), ([8,8], 288)]
theorem targetQuadratic_data : targetQuadratic = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.scale 17 (SparsePolynomial.mul polyTotal polyTotal)) (SparsePolynomial.scale (-121) polySquares)) := by decide +kernel
theorem eval_targetQuadratic (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) targetQuadratic = 17*(total g)^2-121*squareTotal g := by
  rw [targetQuadratic_data]
  simp only [SparsePolynomial.eval_trim, SparsePolynomial.eval_merge, SparsePolynomial.eval_scale, SparsePolynomial.eval_mul, eval_polyTotal, eval_polySquares]
  push_cast
  ring

end APPT.Finite9
