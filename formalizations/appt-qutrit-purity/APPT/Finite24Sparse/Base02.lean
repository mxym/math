import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def base02 : SparsePolynomial.Poly := [([0], -4), ([1], -12), ([2], -16), ([3], -16), ([4], -16), ([5], -16), ([6], -16), ([7], -16), ([8], -16), ([9], -16), ([10], -16), ([11], -16), ([12], -16), ([13], -16), ([14], -16), ([15], -16), ([16], -16), ([17], -16), ([18], -8), ([19], -4), ([20], 4), ([21], 6), ([22], 10), ([23], 18)]
theorem eval_base02 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) base02 = quadA (outer g) ![2,1,2] := by
  norm_num [base02, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, quadA, matA, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base02_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base02 := by
  rw [eval_base02]
  exact quadA_nonneg (outer g) hA ![2,1,2]

end APPT.Finite24
