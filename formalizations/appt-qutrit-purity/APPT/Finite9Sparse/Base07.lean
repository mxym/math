import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def base07 : SparsePolynomial.Poly := [([0], -8), ([1], -12), ([2], -16), ([3], -14), ([4], -10), ([5], -2), ([6], 2), ([7], 10), ([8], 18)]
theorem eval_base07 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) base07 = quadB (outer g) ![2,2,1] := by
  norm_num [base07, SparsePolynomial.eval, SparsePolynomial.mon, variables, spectrum, quadB, matB, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base07_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) base07 := by
  rw [eval_base07]
  exact quadB_nonneg (outer g) hB ![2,2,1]

end APPT.Finite9
