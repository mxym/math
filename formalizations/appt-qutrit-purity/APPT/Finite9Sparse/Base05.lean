import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def base05 : SparsePolynomial.Poly := [([0], -2), ([1], -2), ([2], -2), ([3], -2), ([4], -2), ([7], 2), ([8], 4)]
theorem eval_base05 (g : Fin 9 → ℝ) : SparsePolynomial.eval (variables g) base05 = quadB (outer g) ![1,1,0] := by
  norm_num [base05, SparsePolynomial.eval, SparsePolynomial.mon, variables, spectrum, quadB, matB, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base05_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) base05 := by
  rw [eval_base05]
  exact quadB_nonneg (outer g) hB ![1,1,0]

end APPT.Finite9
