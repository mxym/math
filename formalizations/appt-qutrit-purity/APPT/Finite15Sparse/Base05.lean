import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def base05 : SparsePolynomial.Poly := [([0,0], -1), ([0,1], -2), ([0,2], -2), ([0,3], -2), ([0,4], -2), ([0,5], -2), ([0,6], -2), ([0,7], -2), ([0,8], -2), ([0,9], -2), ([0,10], -2), ([0,11], -2), ([0,12], -2), ([1,1], -1), ([1,2], -2), ([1,3], -2), ([1,4], -2), ([1,5], -2), ([1,6], -2), ([1,7], -2), ([1,8], -2), ([1,9], -2), ([1,10], -2), ([1,11], -2), ([1,12], -2), ([2,2], -1), ([2,3], -2), ([2,4], -2), ([2,5], -2), ([2,6], -2), ([2,7], -2), ([2,8], -2), ([2,9], -2), ([2,10], -2), ([2,11], -2), ([2,12], -2), ([3,3], -1), ([3,4], -2), ([3,5], -2), ([3,6], -2), ([3,7], -2), ([3,8], -2), ([3,9], -2), ([3,10], -2), ([3,11], -2), ([3,12], -2), ([4,4], -1), ([4,5], -2), ([4,6], -2), ([4,7], -2), ([4,8], -2), ([4,9], -2), ([4,10], -2), ([4,11], -2), ([4,12], -2), ([5,5], -1), ([5,6], -2), ([5,7], -2), ([5,8], -2), ([5,9], -2), ([5,10], -2), ([5,11], -2), ([5,12], -2), ([6,6], -1), ([6,7], -2), ([6,8], -2), ([6,9], -2), ([6,10], -2), ([6,11], -2), ([6,12], -2), ([7,7], -1), ([7,8], -2), ([7,9], -2), ([7,10], -2), ([7,11], -2), ([7,12], -2), ([8,8], -1), ([8,9], -2), ([8,10], -2), ([8,11], -2), ([8,12], -2), ([9,9], -1), ([9,10], -2), ([9,11], -2), ([9,12], -2), ([10,10], -1), ([10,11], -2), ([10,12], -2), ([11,11], -1), ([11,12], -2), ([11,14], 4), ([12,12], -1), ([12,14], 4), ([13,14], 4), ([14,14], 4)]
theorem base05_data : base05 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.mul entryB00 entryB11) (SparsePolynomial.scale (-1) (SparsePolynomial.mul entryB01 entryB10))) := by decide +kernel
theorem eval_base05 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) base05 = minorB (outer g) 0 1 := by
  rw [base05_data]
  simp only [SparsePolynomial.eval_trim, SparsePolynomial.eval_merge, SparsePolynomial.eval_scale, SparsePolynomial.eval_mul, eval_entryB00, eval_entryB01, eval_entryB02, eval_entryB10, eval_entryB11, eval_entryB12, eval_entryB20, eval_entryB21, eval_entryB22]
  simp only [minorB]
  push_cast
  ring
theorem base05_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base05 := by
  rw [eval_base05]
  exact minorB_nonneg (outer g) hB 0 1

end APPT.Finite15
