import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def base01 : SparsePolynomial.Poly := [([0], -4), ([1], -8), ([2], -16), ([3], -16), ([4], -16), ([5], -16), ([6], -16), ([7], -16), ([8], -16), ([9], -16), ([10], -16), ([11], -16), ([12], -16), ([13], -16), ([14], -16), ([15], -16), ([16], -16), ([17], -16), ([18], -8), ([20], 4), ([21], 12), ([22], 16), ([23], 18)]
theorem eval_base01 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) base01 = quadA (outer g) ![1,2,2] := by
  norm_num [base01, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, quadA, matA, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base01_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base01 := by
  rw [eval_base01]
  exact quadA_nonneg (outer g) hA ![1,2,2]

end APPT.Finite24
