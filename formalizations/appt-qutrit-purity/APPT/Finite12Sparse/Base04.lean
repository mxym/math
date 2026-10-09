import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def base04 : SparsePolynomial.Poly := [([0,0], -1), ([0,1], -2), ([0,2], -2), ([0,3], -2), ([0,4], -2), ([0,5], -2), ([0,6], -2), ([0,7], -2), ([0,8], -2), ([0,9], -2), ([1,1], -1), ([1,2], -2), ([1,3], -2), ([1,4], -2), ([1,5], -2), ([1,6], -2), ([1,7], -2), ([1,8], -2), ([1,9], -2), ([2,2], -1), ([2,3], -2), ([2,4], -2), ([2,5], -2), ([2,6], -2), ([2,7], -2), ([2,8], -2), ([2,9], -2), ([3,3], -1), ([3,4], -2), ([3,5], -2), ([3,6], -2), ([3,7], -2), ([3,8], -2), ([3,9], -2), ([4,4], -1), ([4,5], -2), ([4,6], -2), ([4,7], -2), ([4,8], -2), ([4,9], -2), ([5,5], -1), ([5,6], -2), ([5,7], -2), ([5,8], -2), ([5,9], -2), ([6,6], -1), ([6,7], -2), ([6,8], -2), ([6,9], -2), ([7,7], -1), ([7,8], -2), ([7,9], -2), ([8,8], -1), ([8,9], -2), ([8,11], 4), ([9,9], -1), ([9,11], 4), ([10,11], 4), ([11,11], 4)]
theorem base04_data : base04 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.mul entryB00 entryB11) (SparsePolynomial.scale (-1) (SparsePolynomial.mul entryB01 entryB10))) := by decide +kernel
theorem eval_base04 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) base04 = minorB (outer g) 0 1 := by
  rw [base04_data]
  simp only [SparsePolynomial.eval_trim, SparsePolynomial.eval_merge, SparsePolynomial.eval_scale, SparsePolynomial.eval_mul, eval_entryB00, eval_entryB01, eval_entryB02, eval_entryB10, eval_entryB11, eval_entryB12, eval_entryB20, eval_entryB21, eval_entryB22]
  simp only [minorB]
  push_cast
  ring
theorem base04_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) base04 := by
  rw [eval_base04]
  exact minorB_nonneg (outer g) hB 0 1

end APPT.Finite12
