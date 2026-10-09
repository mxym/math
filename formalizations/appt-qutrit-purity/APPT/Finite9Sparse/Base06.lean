import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def base06 : SparsePolynomial.Poly := [([0], -4), ([1], -8), ([2], -16), ([3], -8), ([5], 8), ([6], 12), ([7], 16), ([8], 18)]
theorem eval_base06 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) base06 = quadB (outer g) ![1,2,2] := by
  norm_num [base06, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, quadB, matB, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base06_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base06 := by
  rw [eval_base06]
  exact quadB_nonneg (outer g) hB ![1,2,2]

end APPT.Finite9
