import APPT.Finite12Sparse.Moments
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def targetQuadratic : SparsePolynomial.Poly := [([0,0], -176), ([0,1], -312), ([0,2], -272), ([0,3], -232), ([0,4], -192), ([0,5], -152), ([0,6], -112), ([0,7], -72), ([0,8], -32), ([0,9], 8), ([0,10], 48), ([0,11], 88), ([1,1], -312), ([1,2], -544), ([1,3], -464), ([1,4], -384), ([1,5], -304), ([1,6], -224), ([1,7], -144), ([1,8], -64), ([1,9], 16), ([1,10], 96), ([1,11], 176), ([2,2], -408), ([2,3], -696), ([2,4], -576), ([2,5], -456), ([2,6], -336), ([2,7], -216), ([2,8], -96), ([2,9], 24), ([2,10], 144), ([2,11], 264), ([3,3], -464), ([3,4], -768), ([3,5], -608), ([3,6], -448), ([3,7], -288), ([3,8], -128), ([3,9], 32), ([3,10], 192), ([3,11], 352), ([4,4], -480), ([4,5], -760), ([4,6], -560), ([4,7], -360), ([4,8], -160), ([4,9], 40), ([4,10], 240), ([4,11], 440), ([5,5], -456), ([5,6], -672), ([5,7], -432), ([5,8], -192), ([5,9], 48), ([5,10], 288), ([5,11], 528), ([6,6], -392), ([6,7], -504), ([6,8], -224), ([6,9], 56), ([6,10], 336), ([6,11], 616), ([7,7], -288), ([7,8], -256), ([7,9], 64), ([7,10], 384), ([7,11], 704), ([8,8], -144), ([8,9], 72), ([8,10], 432), ([8,11], 792), ([9,9], 40), ([9,10], 480), ([9,11], 880), ([10,10], 264), ([10,11], 968), ([11,11], 528)]
theorem targetQuadratic_data : targetQuadratic = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.scale 20 (SparsePolynomial.mul polyTotal polyTotal)) (SparsePolynomial.scale (-196) polySquares)) := by decide +kernel
theorem eval_targetQuadratic (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) targetQuadratic = 20*(total g)^2-196*squareTotal g := by
  rw [targetQuadratic_data]
  simp only [SparsePolynomial.eval_trim, SparsePolynomial.eval_merge, SparsePolynomial.eval_scale, SparsePolynomial.eval_mul, eval_polyTotal, eval_polySquares]
  push_cast
  ring

end APPT.Finite12
