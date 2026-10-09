import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def base01 : SparsePolynomial.Poly := [([0], -4), ([1], -12), ([2], -16), ([3], -8), ([4], -4), ([5], 4), ([6], 6), ([7], 10), ([8], 18)]
theorem eval_base01 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) base01 = quadA (outer g) ![2,1,2] := by
  norm_num [base01, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, quadA, matA, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base01_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base01 := by
  rw [eval_base01]
  exact quadA_nonneg (outer g) hA ![2,1,2]

end APPT.Finite9
