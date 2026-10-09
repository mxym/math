import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def base03 : SparsePolynomial.Poly := [([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,1,2], -2), ([0,1,3], -6), ([0,1,4], -4), ([0,1,5], -4), ([0,1,6], -4), ([0,1,7], -4), ([0,1,8], -4), ([0,2,2], -2), ([0,2,3], -8), ([0,2,4], -6), ([0,2,5], -6), ([0,2,6], -4), ([0,2,7], -4), ([0,2,8], -4), ([0,3,3], -6), ([0,3,4], -10), ([0,3,5], -10), ([0,3,6], -8), ([0,3,7], -4), ([0,3,8], -4), ([0,4,4], -4), ([0,4,5], -8), ([0,4,6], -8), ([0,4,7], -4), ([0,4,8], -4), ([0,5,5], -4), ([0,5,6], -8), ([0,5,7], -4), ([0,5,8], -4), ([0,6,6], -4), ([0,6,7], -4), ([0,6,8], -4), ([1,1,2], -2), ([1,1,3], -4), ([1,1,4], -2), ([1,1,5], -4), ([1,1,6], -4), ([1,1,7], -4), ([1,1,8], -4), ([1,2,2], -4), ([1,2,3], -12), ([1,2,4], -8), ([1,2,5], -12), ([1,2,6], -10), ([1,2,7], -8), ([1,2,8], -8), ([1,3,3], -8), ([1,3,4], -12), ([1,3,5], -16), ([1,3,6], -14), ([1,3,7], -8), ([1,3,8], -8), ([1,4,4], -4), ([1,4,5], -12), ([1,4,6], -12), ([1,4,7], -8), ([1,4,8], -8), ([1,5,5], -8), ([1,5,6], -12), ([1,5,7], -8), ([1,5,8], -8), ([1,6,6], -4), ([1,6,7], -4), ([1,6,8], -4), ([2,2,2], -2), ([2,2,3], -8), ([2,2,4], -6), ([2,2,5], -8), ([2,2,6], -6), ([2,2,7], -4), ([2,2,8], -6), ([2,3,3], -10), ([2,3,4], -16), ([2,3,5], -20), ([2,3,6], -16), ([2,3,7], -8), ([2,3,8], -12), ([2,4,4], -6), ([2,4,5], -16), ([2,4,6], -14), ([2,4,7], -8), ([2,4,8], -8), ([2,5,5], -10), ([2,5,6], -14), ([2,5,7], -8), ([2,5,8], -8), ([2,6,6], -4), ([2,6,7], -4), ([2,6,8], -4), ([3,3,3], -4), ([3,3,4], -10), ([3,3,5], -12), ([3,3,6], -10), ([3,3,7], -4), ([3,3,8], -6), ([3,4,4], -8), ([3,4,5], -20), ([3,4,6], -18), ([3,4,7], -8), ([3,4,8], -8), ([3,5,5], -12), ([3,5,6], -18), ([3,5,7], -8), ([3,6,6], -6), ([3,6,7], -4), ([3,6,8], 4), ([3,7,8], 8), ([3,8,8], 8), ([4,4,4], -2), ([4,4,5], -8), ([4,4,6], -8), ([4,4,7], -4), ([4,4,8], -4), ([4,5,5], -10), ([4,5,6], -16), ([4,5,7], -8), ([4,6,6], -6), ([4,6,7], -4), ([4,6,8], 4), ([4,7,8], 8), ([4,8,8], 8), ([5,5,5], -4), ([5,5,6], -8), ([5,5,7], -4), ([5,5,8], 4), ([5,6,6], -6), ([5,6,7], -4), ([5,6,8], 12), ([5,7,8], 16), ([5,8,8], 16), ([6,6,6], -2), ([6,6,7], -2), ([6,6,8], 6), ([6,7,8], 16), ([6,8,8], 16), ([7,7,8], 8), ([7,8,8], 16), ([8,8,8], 8)]
theorem base03_data : base03 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.mul entryB00 (SparsePolynomial.mul entryB11 entryB22)) (SparsePolynomial.merge (SparsePolynomial.mul entryB01 (SparsePolynomial.mul entryB12 entryB20)) (SparsePolynomial.mul entryB02 (SparsePolynomial.mul entryB10 entryB21)))) (SparsePolynomial.merge (SparsePolynomial.scale (-1) (SparsePolynomial.mul entryB02 (SparsePolynomial.mul entryB11 entryB20))) (SparsePolynomial.merge (SparsePolynomial.scale (-1) (SparsePolynomial.mul entryB01 (SparsePolynomial.mul entryB10 entryB22))) (SparsePolynomial.scale (-1) (SparsePolynomial.mul entryB00 (SparsePolynomial.mul entryB12 entryB21)))))) := by decide +kernel
theorem eval_base03 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) base03 = detB (outer g) := by
  rw [base03_data]
  simp only [SparsePolynomial.eval_trim, SparsePolynomial.eval_merge, SparsePolynomial.eval_scale, SparsePolynomial.eval_mul, eval_entryB00, eval_entryB01, eval_entryB02, eval_entryB10, eval_entryB11, eval_entryB12, eval_entryB20, eval_entryB21, eval_entryB22]
  simp only [detB, Matrix.det_fin_three]
  push_cast
  ring
theorem base03_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base03 := by
  rw [eval_base03]
  exact detB_nonneg (outer g) hB

end APPT.Finite9
