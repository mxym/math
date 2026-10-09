import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def base00 : SparsePolynomial.Poly := [([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,1,2], -2), ([0,1,3], -6), ([0,1,4], -4), ([0,1,5], -4), ([0,1,6], -4), ([0,1,7], -4), ([0,1,8], -4), ([0,2,2], -2), ([0,2,3], -8), ([0,2,4], -6), ([0,2,5], -4), ([0,2,6], -4), ([0,2,7], -4), ([0,2,8], -4), ([0,3,3], -6), ([0,3,4], -10), ([0,3,5], -8), ([0,3,6], -8), ([0,3,7], -4), ([0,3,8], -4), ([0,4,4], -4), ([0,4,5], -8), ([0,4,6], -8), ([0,4,7], -4), ([0,4,8], -4), ([0,5,5], -4), ([0,5,6], -8), ([0,5,7], -4), ([0,5,8], -4), ([0,6,6], -4), ([0,6,7], -4), ([0,6,8], -4), ([1,1,2], -2), ([1,1,3], -4), ([1,1,4], -2), ([1,1,5], -2), ([1,1,6], -4), ([1,1,7], -4), ([1,1,8], -4), ([1,2,2], -4), ([1,2,3], -12), ([1,2,4], -8), ([1,2,5], -6), ([1,2,6], -10), ([1,2,7], -8), ([1,2,8], -8), ([1,3,3], -8), ([1,3,4], -12), ([1,3,5], -10), ([1,3,6], -14), ([1,3,7], -8), ([1,3,8], -8), ([1,4,4], -4), ([1,4,5], -8), ([1,4,6], -12), ([1,4,7], -8), ([1,4,8], -8), ([1,5,5], -4), ([1,5,6], -8), ([1,5,7], -4), ([1,5,8], -4), ([1,6,6], -4), ([1,6,7], -4), ([1,6,8], -4), ([2,2,2], -2), ([2,2,3], -8), ([2,2,4], -6), ([2,2,5], -4), ([2,2,6], -6), ([2,2,7], -4), ([2,2,8], -6), ([2,3,3], -10), ([2,3,4], -16), ([2,3,5], -12), ([2,3,6], -16), ([2,3,7], -8), ([2,3,8], -12), ([2,4,4], -6), ([2,4,5], -10), ([2,4,6], -14), ([2,4,7], -8), ([2,4,8], -8), ([2,5,5], -4), ([2,5,6], -8), ([2,5,7], -4), ([2,5,8], -4), ([2,6,6], -4), ([2,6,7], -4), ([2,6,8], -4), ([3,3,3], -4), ([3,3,4], -10), ([3,3,5], -8), ([3,3,6], -10), ([3,3,7], -4), ([3,3,8], -6), ([3,4,4], -8), ([3,4,5], -14), ([3,4,6], -18), ([3,4,7], -8), ([3,4,8], -8), ([3,5,5], -6), ([3,5,6], -12), ([3,5,7], -4), ([3,5,8], -4), ([3,6,6], -6), ([3,6,7], -4), ([3,6,8], 4), ([3,7,8], 8), ([3,8,8], 8), ([4,4,4], -2), ([4,4,5], -6), ([4,4,6], -8), ([4,4,7], -4), ([4,4,8], -4), ([4,5,5], -6), ([4,5,6], -12), ([4,5,7], -4), ([4,5,8], -4), ([4,6,6], -6), ([4,6,7], -4), ([4,6,8], 4), ([4,7,8], 8), ([4,8,8], 8), ([5,5,5], -2), ([5,5,6], -6), ([5,5,7], -2), ([5,5,8], -2), ([5,6,6], -6), ([5,6,7], -4), ([5,6,8], 4), ([5,7,8], 8), ([5,8,8], 8), ([6,6,6], -2), ([6,6,7], -2), ([6,6,8], 6), ([6,7,8], 16), ([6,8,8], 16), ([7,7,8], 8), ([7,8,8], 16), ([8,8,8], 8)]
theorem base00_data : base00 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.mul entryA00 (SparsePolynomial.mul entryA11 entryA22)) (SparsePolynomial.merge (SparsePolynomial.mul entryA01 (SparsePolynomial.mul entryA12 entryA20)) (SparsePolynomial.mul entryA02 (SparsePolynomial.mul entryA10 entryA21)))) (SparsePolynomial.merge (SparsePolynomial.scale (-1) (SparsePolynomial.mul entryA02 (SparsePolynomial.mul entryA11 entryA20))) (SparsePolynomial.merge (SparsePolynomial.scale (-1) (SparsePolynomial.mul entryA01 (SparsePolynomial.mul entryA10 entryA22))) (SparsePolynomial.scale (-1) (SparsePolynomial.mul entryA00 (SparsePolynomial.mul entryA12 entryA21)))))) := by decide +kernel
theorem eval_base00 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) base00 = detA (outer g) := by
  rw [base00_data]
  simp only [SparsePolynomial.eval_trim, SparsePolynomial.eval_merge, SparsePolynomial.eval_scale, SparsePolynomial.eval_mul, eval_entryA00, eval_entryA01, eval_entryA02, eval_entryA10, eval_entryA11, eval_entryA12, eval_entryA20, eval_entryA21, eval_entryA22]
  simp only [detA, Matrix.det_fin_three]
  push_cast
  ring
theorem base00_nonneg (g : Fin 9 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base00 := by
  rw [eval_base00]
  exact detA_nonneg (outer g) hA

end APPT.Finite9
