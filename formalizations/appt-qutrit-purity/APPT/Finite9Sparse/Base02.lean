import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def base02 : SparsePolynomial.Poly := [([0], -8), ([1], -12), ([2], -16), ([3], -14), ([4], -10), ([5], -6), ([6], 2), ([7], 10), ([8], 18)]
theorem eval_base02 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) base02 = quadA (outer g) ![2,2,1] := by
  norm_num [base02, SparsePolynomial.eval, SparsePolynomial.mon, variables, spectrum, quadA, matA, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base02_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) base02 := by
  rw [eval_base02]
  exact quadA_nonneg (outer g) hA ![2,2,1]

end APPT.Finite9
