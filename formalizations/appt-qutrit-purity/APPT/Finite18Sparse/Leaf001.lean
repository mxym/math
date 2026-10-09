import APPT.Finite18Sparse.Base05
import APPT.Finite18Sparse.Base06
import APPT.Finite18Sparse.Base07
import APPT.Finite18Sparse.Base08
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0015 : SparsePolynomial.Poly := [([0,0,0], -1), ([0,0,1], -2), ([0,0,2], -2), ([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,0,9], -2), ([0,0,10], -2), ([0,0,11], -2), ([0,0,12], -2), ([0,0,13], -2), ([0,0,14], -2), ([0,0,15], -2), ([0,1,1], -1), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -2), ([0,1,7], -2), ([0,1,8], -2), ([0,1,9], -2), ([0,1,10], -2), ([0,1,11], -2), ([0,1,12], -2), ([0,1,13], -2), ([0,1,14], -2), ([0,1,15], -2), ([0,2,2], -1), ([0,2,3], -2), ([0,2,4], -2), ([0,2,5], -2), ([0,2,6], -2), ([0,2,7], -2), ([0,2,8], -2), ([0,2,9], -2), ([0,2,10], -2), ([0,2,11], -2), ([0,2,12], -2), ([0,2,13], -2), ([0,2,14], -2), ([0,2,15], -2), ([0,3,3], -1), ([0,3,4], -2), ([0,3,5], -2), ([0,3,6], -2), ([0,3,7], -2), ([0,3,8], -2), ([0,3,9], -2), ([0,3,10], -2), ([0,3,11], -2), ([0,3,12], -2), ([0,3,13], -2), ([0,3,14], -2), ([0,3,15], -2), ([0,4,4], -1), ([0,4,5], -2), ([0,4,6], -2), ([0,4,7], -2), ([0,4,8], -2), ([0,4,9], -2), ([0,4,10], -2), ([0,4,11], -2), ([0,4,12], -2), ([0,4,13], -2), ([0,4,14], -2), ([0,4,15], -2), ([0,5,5], -1), ([0,5,6], -2), ([0,5,7], -2), ([0,5,8], -2), ([0,5,9], -2), ([0,5,10], -2), ([0,5,11], -2), ([0,5,12], -2), ([0,5,13], -2), ([0,5,14], -2), ([0,5,15], -2), ([0,6,6], -1), ([0,6,7], -2), ([0,6,8], -2), ([0,6,9], -2), ([0,6,10], -2), ([0,6,11], -2), ([0,6,12], -2), ([0,6,13], -2), ([0,6,14], -2), ([0,6,15], -2), ([0,7,7], -1), ([0,7,8], -2), ([0,7,9], -2), ([0,7,10], -2), ([0,7,11], -2), ([0,7,12], -2), ([0,7,13], -2), ([0,7,14], -2), ([0,7,15], -2), ([0,8,8], -1), ([0,8,9], -2), ([0,8,10], -2), ([0,8,11], -2), ([0,8,12], -2), ([0,8,13], -2), ([0,8,14], -2), ([0,8,15], -2), ([0,9,9], -1), ([0,9,10], -2), ([0,9,11], -2), ([0,9,12], -2), ([0,9,13], -2), ([0,9,14], -2), ([0,9,15], -2), ([0,10,10], -1), ([0,10,11], -2), ([0,10,12], -2), ([0,10,13], -2), ([0,10,14], -2), ([0,10,15], -2), ([0,11,11], -1), ([0,11,12], -2), ([0,11,13], -2), ([0,11,14], -2), ([0,11,15], -2), ([0,12,12], -1), ([0,12,13], -2), ([0,12,14], -2), ([0,12,15], -2), ([0,13,13], -1), ([0,13,14], -2), ([0,13,15], -2), ([0,14,14], -1), ([0,14,15], -2), ([0,14,17], 4), ([0,15,15], -1), ([0,15,17], 4), ([0,16,17], 4), ([0,17,17], 4)]
theorem atom0015_data : atom0015 = SparsePolynomial.monoTimes [0] 1 base05 := by decide +kernel
theorem eval_atom0015 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0015 = (minorB (outer g) 0 1 * g 0) := by
  rw [atom0015_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0015_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (120637440 : Int) atom0015) := by
  rw [SparsePolynomial.eval_scale, eval_atom0015]
  have hg0 : 0 ≤ g 0 := hg 0
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 0) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0016 : SparsePolynomial.Poly := [([0,0,8], -1), ([0,1,8], -2), ([0,2,8], -2), ([0,3,8], -2), ([0,4,8], -2), ([0,5,8], -2), ([0,6,8], -2), ([0,7,8], -2), ([0,8,8], -2), ([0,8,9], -2), ([0,8,10], -2), ([0,8,11], -2), ([0,8,12], -2), ([0,8,13], -2), ([0,8,14], -2), ([0,8,15], -2), ([1,1,8], -1), ([1,2,8], -2), ([1,3,8], -2), ([1,4,8], -2), ([1,5,8], -2), ([1,6,8], -2), ([1,7,8], -2), ([1,8,8], -2), ([1,8,9], -2), ([1,8,10], -2), ([1,8,11], -2), ([1,8,12], -2), ([1,8,13], -2), ([1,8,14], -2), ([1,8,15], -2), ([2,2,8], -1), ([2,3,8], -2), ([2,4,8], -2), ([2,5,8], -2), ([2,6,8], -2), ([2,7,8], -2), ([2,8,8], -2), ([2,8,9], -2), ([2,8,10], -2), ([2,8,11], -2), ([2,8,12], -2), ([2,8,13], -2), ([2,8,14], -2), ([2,8,15], -2), ([3,3,8], -1), ([3,4,8], -2), ([3,5,8], -2), ([3,6,8], -2), ([3,7,8], -2), ([3,8,8], -2), ([3,8,9], -2), ([3,8,10], -2), ([3,8,11], -2), ([3,8,12], -2), ([3,8,13], -2), ([3,8,14], -2), ([3,8,15], -2), ([4,4,8], -1), ([4,5,8], -2), ([4,6,8], -2), ([4,7,8], -2), ([4,8,8], -2), ([4,8,9], -2), ([4,8,10], -2), ([4,8,11], -2), ([4,8,12], -2), ([4,8,13], -2), ([4,8,14], -2), ([4,8,15], -2), ([5,5,8], -1), ([5,6,8], -2), ([5,7,8], -2), ([5,8,8], -2), ([5,8,9], -2), ([5,8,10], -2), ([5,8,11], -2), ([5,8,12], -2), ([5,8,13], -2), ([5,8,14], -2), ([5,8,15], -2), ([6,6,8], -1), ([6,7,8], -2), ([6,8,8], -2), ([6,8,9], -2), ([6,8,10], -2), ([6,8,11], -2), ([6,8,12], -2), ([6,8,13], -2), ([6,8,14], -2), ([6,8,15], -2), ([7,7,8], -1), ([7,8,8], -2), ([7,8,9], -2), ([7,8,10], -2), ([7,8,11], -2), ([7,8,12], -2), ([7,8,13], -2), ([7,8,14], -2), ([7,8,15], -2), ([8,8,8], -1), ([8,8,9], -2), ([8,8,10], -2), ([8,8,11], -2), ([8,8,12], -2), ([8,8,13], -2), ([8,8,14], -2), ([8,8,15], -2), ([8,9,9], -1), ([8,9,10], -2), ([8,9,11], -2), ([8,9,12], -2), ([8,9,13], -2), ([8,9,14], -2), ([8,9,15], -2), ([8,10,10], -1), ([8,10,11], -2), ([8,10,12], -2), ([8,10,13], -2), ([8,10,14], -2), ([8,10,15], -2), ([8,11,11], -1), ([8,11,12], -2), ([8,11,13], -2), ([8,11,14], -2), ([8,11,15], -2), ([8,12,12], -1), ([8,12,13], -2), ([8,12,14], -2), ([8,12,15], -2), ([8,13,13], -1), ([8,13,14], -2), ([8,13,15], -2), ([8,14,14], -1), ([8,14,15], -2), ([8,14,17], 4), ([8,15,15], -1), ([8,15,17], 4), ([8,16,17], 4), ([8,17,17], 4)]
theorem atom0016_data : atom0016 = SparsePolynomial.monoTimes [8] 1 base05 := by decide +kernel
theorem eval_atom0016 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0016 = (minorB (outer g) 0 1 * g 8) := by
  rw [atom0016_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0016_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (51233280 : Int) atom0016) := by
  rw [SparsePolynomial.eval_scale, eval_atom0016]
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0017 : SparsePolynomial.Poly := [([0,0,9], -1), ([0,1,9], -2), ([0,2,9], -2), ([0,3,9], -2), ([0,4,9], -2), ([0,5,9], -2), ([0,6,9], -2), ([0,7,9], -2), ([0,8,9], -2), ([0,9,9], -2), ([0,9,10], -2), ([0,9,11], -2), ([0,9,12], -2), ([0,9,13], -2), ([0,9,14], -2), ([0,9,15], -2), ([1,1,9], -1), ([1,2,9], -2), ([1,3,9], -2), ([1,4,9], -2), ([1,5,9], -2), ([1,6,9], -2), ([1,7,9], -2), ([1,8,9], -2), ([1,9,9], -2), ([1,9,10], -2), ([1,9,11], -2), ([1,9,12], -2), ([1,9,13], -2), ([1,9,14], -2), ([1,9,15], -2), ([2,2,9], -1), ([2,3,9], -2), ([2,4,9], -2), ([2,5,9], -2), ([2,6,9], -2), ([2,7,9], -2), ([2,8,9], -2), ([2,9,9], -2), ([2,9,10], -2), ([2,9,11], -2), ([2,9,12], -2), ([2,9,13], -2), ([2,9,14], -2), ([2,9,15], -2), ([3,3,9], -1), ([3,4,9], -2), ([3,5,9], -2), ([3,6,9], -2), ([3,7,9], -2), ([3,8,9], -2), ([3,9,9], -2), ([3,9,10], -2), ([3,9,11], -2), ([3,9,12], -2), ([3,9,13], -2), ([3,9,14], -2), ([3,9,15], -2), ([4,4,9], -1), ([4,5,9], -2), ([4,6,9], -2), ([4,7,9], -2), ([4,8,9], -2), ([4,9,9], -2), ([4,9,10], -2), ([4,9,11], -2), ([4,9,12], -2), ([4,9,13], -2), ([4,9,14], -2), ([4,9,15], -2), ([5,5,9], -1), ([5,6,9], -2), ([5,7,9], -2), ([5,8,9], -2), ([5,9,9], -2), ([5,9,10], -2), ([5,9,11], -2), ([5,9,12], -2), ([5,9,13], -2), ([5,9,14], -2), ([5,9,15], -2), ([6,6,9], -1), ([6,7,9], -2), ([6,8,9], -2), ([6,9,9], -2), ([6,9,10], -2), ([6,9,11], -2), ([6,9,12], -2), ([6,9,13], -2), ([6,9,14], -2), ([6,9,15], -2), ([7,7,9], -1), ([7,8,9], -2), ([7,9,9], -2), ([7,9,10], -2), ([7,9,11], -2), ([7,9,12], -2), ([7,9,13], -2), ([7,9,14], -2), ([7,9,15], -2), ([8,8,9], -1), ([8,9,9], -2), ([8,9,10], -2), ([8,9,11], -2), ([8,9,12], -2), ([8,9,13], -2), ([8,9,14], -2), ([8,9,15], -2), ([9,9,9], -1), ([9,9,10], -2), ([9,9,11], -2), ([9,9,12], -2), ([9,9,13], -2), ([9,9,14], -2), ([9,9,15], -2), ([9,10,10], -1), ([9,10,11], -2), ([9,10,12], -2), ([9,10,13], -2), ([9,10,14], -2), ([9,10,15], -2), ([9,11,11], -1), ([9,11,12], -2), ([9,11,13], -2), ([9,11,14], -2), ([9,11,15], -2), ([9,12,12], -1), ([9,12,13], -2), ([9,12,14], -2), ([9,12,15], -2), ([9,13,13], -1), ([9,13,14], -2), ([9,13,15], -2), ([9,14,14], -1), ([9,14,15], -2), ([9,14,17], 4), ([9,15,15], -1), ([9,15,17], 4), ([9,16,17], 4), ([9,17,17], 4)]
theorem atom0017_data : atom0017 = SparsePolynomial.monoTimes [9] 1 base05 := by decide +kernel
theorem eval_atom0017 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0017 = (minorB (outer g) 0 1 * g 9) := by
  rw [atom0017_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0017_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42201600 : Int) atom0017) := by
  rw [SparsePolynomial.eval_scale, eval_atom0017]
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0018 : SparsePolynomial.Poly := [([0,0,10], -1), ([0,1,10], -2), ([0,2,10], -2), ([0,3,10], -2), ([0,4,10], -2), ([0,5,10], -2), ([0,6,10], -2), ([0,7,10], -2), ([0,8,10], -2), ([0,9,10], -2), ([0,10,10], -2), ([0,10,11], -2), ([0,10,12], -2), ([0,10,13], -2), ([0,10,14], -2), ([0,10,15], -2), ([1,1,10], -1), ([1,2,10], -2), ([1,3,10], -2), ([1,4,10], -2), ([1,5,10], -2), ([1,6,10], -2), ([1,7,10], -2), ([1,8,10], -2), ([1,9,10], -2), ([1,10,10], -2), ([1,10,11], -2), ([1,10,12], -2), ([1,10,13], -2), ([1,10,14], -2), ([1,10,15], -2), ([2,2,10], -1), ([2,3,10], -2), ([2,4,10], -2), ([2,5,10], -2), ([2,6,10], -2), ([2,7,10], -2), ([2,8,10], -2), ([2,9,10], -2), ([2,10,10], -2), ([2,10,11], -2), ([2,10,12], -2), ([2,10,13], -2), ([2,10,14], -2), ([2,10,15], -2), ([3,3,10], -1), ([3,4,10], -2), ([3,5,10], -2), ([3,6,10], -2), ([3,7,10], -2), ([3,8,10], -2), ([3,9,10], -2), ([3,10,10], -2), ([3,10,11], -2), ([3,10,12], -2), ([3,10,13], -2), ([3,10,14], -2), ([3,10,15], -2), ([4,4,10], -1), ([4,5,10], -2), ([4,6,10], -2), ([4,7,10], -2), ([4,8,10], -2), ([4,9,10], -2), ([4,10,10], -2), ([4,10,11], -2), ([4,10,12], -2), ([4,10,13], -2), ([4,10,14], -2), ([4,10,15], -2), ([5,5,10], -1), ([5,6,10], -2), ([5,7,10], -2), ([5,8,10], -2), ([5,9,10], -2), ([5,10,10], -2), ([5,10,11], -2), ([5,10,12], -2), ([5,10,13], -2), ([5,10,14], -2), ([5,10,15], -2), ([6,6,10], -1), ([6,7,10], -2), ([6,8,10], -2), ([6,9,10], -2), ([6,10,10], -2), ([6,10,11], -2), ([6,10,12], -2), ([6,10,13], -2), ([6,10,14], -2), ([6,10,15], -2), ([7,7,10], -1), ([7,8,10], -2), ([7,9,10], -2), ([7,10,10], -2), ([7,10,11], -2), ([7,10,12], -2), ([7,10,13], -2), ([7,10,14], -2), ([7,10,15], -2), ([8,8,10], -1), ([8,9,10], -2), ([8,10,10], -2), ([8,10,11], -2), ([8,10,12], -2), ([8,10,13], -2), ([8,10,14], -2), ([8,10,15], -2), ([9,9,10], -1), ([9,10,10], -2), ([9,10,11], -2), ([9,10,12], -2), ([9,10,13], -2), ([9,10,14], -2), ([9,10,15], -2), ([10,10,10], -1), ([10,10,11], -2), ([10,10,12], -2), ([10,10,13], -2), ([10,10,14], -2), ([10,10,15], -2), ([10,11,11], -1), ([10,11,12], -2), ([10,11,13], -2), ([10,11,14], -2), ([10,11,15], -2), ([10,12,12], -1), ([10,12,13], -2), ([10,12,14], -2), ([10,12,15], -2), ([10,13,13], -1), ([10,13,14], -2), ([10,13,15], -2), ([10,14,14], -1), ([10,14,15], -2), ([10,14,17], 4), ([10,15,15], -1), ([10,15,17], 4), ([10,16,17], 4), ([10,17,17], 4)]
theorem atom0018_data : atom0018 = SparsePolynomial.monoTimes [10] 1 base05 := by decide +kernel
theorem eval_atom0018 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0018 = (minorB (outer g) 0 1 * g 10) := by
  rw [atom0018_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0018_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (58329600 : Int) atom0018) := by
  rw [SparsePolynomial.eval_scale, eval_atom0018]
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0019 : SparsePolynomial.Poly := [([0,0,17], -2), ([0,1,17], -2), ([0,2,17], -2), ([0,3,17], -2), ([0,4,17], -2), ([0,5,17], -2), ([0,6,17], -2), ([0,7,17], -2), ([0,8,17], -2), ([0,9,17], -2), ([0,10,17], -2), ([0,11,17], -2), ([0,12,17], -2), ([0,13,17], -2), ([0,16,17], 2), ([0,17,17], 4)]
theorem atom0019_data : atom0019 = SparsePolynomial.monoTimes [0,17] 1 base06 := by decide +kernel
theorem eval_atom0019 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0019 = (quadB (outer g) ![1,1,0] * g 0 * g 17) := by
  rw [atom0019_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0019_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (175472640 : Int) atom0019) := by
  rw [SparsePolynomial.eval_scale, eval_atom0019]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,1,0] * g 0 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0020 : SparsePolynomial.Poly := [([0,2,16], -4), ([1,2,16], -8), ([2,2,16], -16), ([2,3,16], -16), ([2,4,16], -16), ([2,5,16], -16), ([2,6,16], -16), ([2,7,16], -16), ([2,8,16], -16), ([2,9,16], -16), ([2,10,16], -16), ([2,11,16], -16), ([2,12,16], -8), ([2,14,16], 8), ([2,15,16], 12), ([2,16,16], 16), ([2,16,17], 18)]
theorem atom0020_data : atom0020 = SparsePolynomial.monoTimes [2,16] 1 base07 := by decide +kernel
theorem eval_atom0020 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0020 = (quadB (outer g) ![1,2,2] * g 2 * g 16) := by
  rw [atom0020_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0020_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (93744000 : Int) atom0020) := by
  rw [SparsePolynomial.eval_scale, eval_atom0020]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 2 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0021 : SparsePolynomial.Poly := [([0,3,11], -4), ([1,3,11], -8), ([2,3,11], -16), ([3,3,11], -16), ([3,4,11], -16), ([3,5,11], -16), ([3,6,11], -16), ([3,7,11], -16), ([3,8,11], -16), ([3,9,11], -16), ([3,10,11], -16), ([3,11,11], -16), ([3,11,12], -8), ([3,11,14], 8), ([3,11,15], 12), ([3,11,16], 16), ([3,11,17], 18)]
theorem atom0021_data : atom0021 = SparsePolynomial.monoTimes [3,11] 1 base07 := by decide +kernel
theorem eval_atom0021 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0021 = (quadB (outer g) ![1,2,2] * g 3 * g 11) := by
  rw [atom0021_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0021_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10080000 : Int) atom0021) := by
  rw [SparsePolynomial.eval_scale, eval_atom0021]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0022 : SparsePolynomial.Poly := [([0,3,13], -4), ([1,3,13], -8), ([2,3,13], -16), ([3,3,13], -16), ([3,4,13], -16), ([3,5,13], -16), ([3,6,13], -16), ([3,7,13], -16), ([3,8,13], -16), ([3,9,13], -16), ([3,10,13], -16), ([3,11,13], -16), ([3,12,13], -8), ([3,13,14], 8), ([3,13,15], 12), ([3,13,16], 16), ([3,13,17], 18)]
theorem atom0022_data : atom0022 = SparsePolynomial.monoTimes [3,13] 1 base07 := by decide +kernel
theorem eval_atom0022 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0022 = (quadB (outer g) ![1,2,2] * g 3 * g 13) := by
  rw [atom0022_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0022_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24272640 : Int) atom0022) := by
  rw [SparsePolynomial.eval_scale, eval_atom0022]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0023 : SparsePolynomial.Poly := [([0,3,15], -4), ([1,3,15], -8), ([2,3,15], -16), ([3,3,15], -16), ([3,4,15], -16), ([3,5,15], -16), ([3,6,15], -16), ([3,7,15], -16), ([3,8,15], -16), ([3,9,15], -16), ([3,10,15], -16), ([3,11,15], -16), ([3,12,15], -8), ([3,14,15], 8), ([3,15,15], 12), ([3,15,16], 16), ([3,15,17], 18)]
theorem atom0023_data : atom0023 = SparsePolynomial.monoTimes [3,15] 1 base07 := by decide +kernel
theorem eval_atom0023 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0023 = (quadB (outer g) ![1,2,2] * g 3 * g 15) := by
  rw [atom0023_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0023_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38465280 : Int) atom0023) := by
  rw [SparsePolynomial.eval_scale, eval_atom0023]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0024 : SparsePolynomial.Poly := [([0,3,16], -4), ([1,3,16], -8), ([2,3,16], -16), ([3,3,16], -16), ([3,4,16], -16), ([3,5,16], -16), ([3,6,16], -16), ([3,7,16], -16), ([3,8,16], -16), ([3,9,16], -16), ([3,10,16], -16), ([3,11,16], -16), ([3,12,16], -8), ([3,14,16], 8), ([3,15,16], 12), ([3,16,16], 16), ([3,16,17], 18)]
theorem atom0024_data : atom0024 = SparsePolynomial.monoTimes [3,16] 1 base07 := by decide +kernel
theorem eval_atom0024 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0024 = (quadB (outer g) ![1,2,2] * g 3 * g 16) := by
  rw [atom0024_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0024_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (156602880 : Int) atom0024) := by
  rw [SparsePolynomial.eval_scale, eval_atom0024]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0025 : SparsePolynomial.Poly := [([0,3,17], -4), ([1,3,17], -8), ([2,3,17], -16), ([3,3,17], -16), ([3,4,17], -16), ([3,5,17], -16), ([3,6,17], -16), ([3,7,17], -16), ([3,8,17], -16), ([3,9,17], -16), ([3,10,17], -16), ([3,11,17], -16), ([3,12,17], -8), ([3,14,17], 8), ([3,15,17], 12), ([3,16,17], 16), ([3,17,17], 18)]
theorem atom0025_data : atom0025 = SparsePolynomial.monoTimes [3,17] 1 base07 := by decide +kernel
theorem eval_atom0025 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0025 = (quadB (outer g) ![1,2,2] * g 3 * g 17) := by
  rw [atom0025_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0025_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52657920 : Int) atom0025) := by
  rw [SparsePolynomial.eval_scale, eval_atom0025]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0026 : SparsePolynomial.Poly := [([0,4,5], -4), ([1,4,5], -8), ([2,4,5], -16), ([3,4,5], -16), ([4,4,5], -16), ([4,5,5], -16), ([4,5,6], -16), ([4,5,7], -16), ([4,5,8], -16), ([4,5,9], -16), ([4,5,10], -16), ([4,5,11], -16), ([4,5,12], -8), ([4,5,14], 8), ([4,5,15], 12), ([4,5,16], 16), ([4,5,17], 18)]
theorem atom0026_data : atom0026 = SparsePolynomial.monoTimes [4,5] 1 base07 := by decide +kernel
theorem eval_atom0026 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0026 = (quadB (outer g) ![1,2,2] * g 4 * g 5) := by
  rw [atom0026_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0026_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90171648 : Int) atom0026) := by
  rw [SparsePolynomial.eval_scale, eval_atom0026]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0027 : SparsePolynomial.Poly := [([0,4,6], -4), ([1,4,6], -8), ([2,4,6], -16), ([3,4,6], -16), ([4,4,6], -16), ([4,5,6], -16), ([4,6,6], -16), ([4,6,7], -16), ([4,6,8], -16), ([4,6,9], -16), ([4,6,10], -16), ([4,6,11], -16), ([4,6,12], -8), ([4,6,14], 8), ([4,6,15], 12), ([4,6,16], 16), ([4,6,17], 18)]
theorem atom0027_data : atom0027 = SparsePolynomial.monoTimes [4,6] 1 base07 := by decide +kernel
theorem eval_atom0027 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0027 = (quadB (outer g) ![1,2,2] * g 4 * g 6) := by
  rw [atom0027_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0027_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38064360 : Int) atom0027) := by
  rw [SparsePolynomial.eval_scale, eval_atom0027]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0028 : SparsePolynomial.Poly := [([0,4,7], -4), ([1,4,7], -8), ([2,4,7], -16), ([3,4,7], -16), ([4,4,7], -16), ([4,5,7], -16), ([4,6,7], -16), ([4,7,7], -16), ([4,7,8], -16), ([4,7,9], -16), ([4,7,10], -16), ([4,7,11], -16), ([4,7,12], -8), ([4,7,14], 8), ([4,7,15], 12), ([4,7,16], 16), ([4,7,17], 18)]
theorem atom0028_data : atom0028 = SparsePolynomial.monoTimes [4,7] 1 base07 := by decide +kernel
theorem eval_atom0028 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0028 = (quadB (outer g) ![1,2,2] * g 4 * g 7) := by
  rw [atom0028_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0028_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7113120 : Int) atom0028) := by
  rw [SparsePolynomial.eval_scale, eval_atom0028]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0029 : SparsePolynomial.Poly := [([0,4,11], -4), ([1,4,11], -8), ([2,4,11], -16), ([3,4,11], -16), ([4,4,11], -16), ([4,5,11], -16), ([4,6,11], -16), ([4,7,11], -16), ([4,8,11], -16), ([4,9,11], -16), ([4,10,11], -16), ([4,11,11], -16), ([4,11,12], -8), ([4,11,14], 8), ([4,11,15], 12), ([4,11,16], 16), ([4,11,17], 18)]
theorem atom0029_data : atom0029 = SparsePolynomial.monoTimes [4,11] 1 base07 := by decide +kernel
theorem eval_atom0029 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0029 = (quadB (outer g) ![1,2,2] * g 4 * g 11) := by
  rw [atom0029_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0029_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4653600 : Int) atom0029) := by
  rw [SparsePolynomial.eval_scale, eval_atom0029]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0030 : SparsePolynomial.Poly := [([0,4,13], -4), ([1,4,13], -8), ([2,4,13], -16), ([3,4,13], -16), ([4,4,13], -16), ([4,5,13], -16), ([4,6,13], -16), ([4,7,13], -16), ([4,8,13], -16), ([4,9,13], -16), ([4,10,13], -16), ([4,11,13], -16), ([4,12,13], -8), ([4,13,14], 8), ([4,13,15], 12), ([4,13,16], 16), ([4,13,17], 18)]
theorem atom0030_data : atom0030 = SparsePolynomial.monoTimes [4,13] 1 base07 := by decide +kernel
theorem eval_atom0030 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0030 = (quadB (outer g) ![1,2,2] * g 4 * g 13) := by
  rw [atom0030_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0030_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35739060 : Int) atom0030) := by
  rw [SparsePolynomial.eval_scale, eval_atom0030]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0031 : SparsePolynomial.Poly := [([0,4,15], -4), ([1,4,15], -8), ([2,4,15], -16), ([3,4,15], -16), ([4,4,15], -16), ([4,5,15], -16), ([4,6,15], -16), ([4,7,15], -16), ([4,8,15], -16), ([4,9,15], -16), ([4,10,15], -16), ([4,11,15], -16), ([4,12,15], -8), ([4,14,15], 8), ([4,15,15], 12), ([4,15,16], 16), ([4,15,17], 18)]
theorem atom0031_data : atom0031 = SparsePolynomial.monoTimes [4,15] 1 base07 := by decide +kernel
theorem eval_atom0031 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0031 = (quadB (outer g) ![1,2,2] * g 4 * g 15) := by
  rw [atom0031_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0031_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (95893980 : Int) atom0031) := by
  rw [SparsePolynomial.eval_scale, eval_atom0031]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0032 : SparsePolynomial.Poly := [([0,4,16], -4), ([1,4,16], -8), ([2,4,16], -16), ([3,4,16], -16), ([4,4,16], -16), ([4,5,16], -16), ([4,6,16], -16), ([4,7,16], -16), ([4,8,16], -16), ([4,9,16], -16), ([4,10,16], -16), ([4,11,16], -16), ([4,12,16], -8), ([4,14,16], 8), ([4,15,16], 12), ([4,16,16], 16), ([4,16,17], 18)]
theorem atom0032_data : atom0032 = SparsePolynomial.monoTimes [4,16] 1 base07 := by decide +kernel
theorem eval_atom0032 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0032 = (quadB (outer g) ![1,2,2] * g 4 * g 16) := by
  rw [atom0032_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0032_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (164598700 : Int) atom0032) := by
  rw [SparsePolynomial.eval_scale, eval_atom0032]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0033 : SparsePolynomial.Poly := [([0,4,17], -4), ([1,4,17], -8), ([2,4,17], -16), ([3,4,17], -16), ([4,4,17], -16), ([4,5,17], -16), ([4,6,17], -16), ([4,7,17], -16), ([4,8,17], -16), ([4,9,17], -16), ([4,10,17], -16), ([4,11,17], -16), ([4,12,17], -8), ([4,14,17], 8), ([4,15,17], 12), ([4,16,17], 16), ([4,17,17], 18)]
theorem atom0033_data : atom0033 = SparsePolynomial.monoTimes [4,17] 1 base07 := by decide +kernel
theorem eval_atom0033 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0033 = (quadB (outer g) ![1,2,2] * g 4 * g 17) := by
  rw [atom0033_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0033_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (175428540 : Int) atom0033) := by
  rw [SparsePolynomial.eval_scale, eval_atom0033]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0034 : SparsePolynomial.Poly := [([0,5,6], -4), ([1,5,6], -8), ([2,5,6], -16), ([3,5,6], -16), ([4,5,6], -16), ([5,5,6], -16), ([5,6,6], -16), ([5,6,7], -16), ([5,6,8], -16), ([5,6,9], -16), ([5,6,10], -16), ([5,6,11], -16), ([5,6,12], -8), ([5,6,14], 8), ([5,6,15], 12), ([5,6,16], 16), ([5,6,17], 18)]
theorem atom0034_data : atom0034 = SparsePolynomial.monoTimes [5,6] 1 base07 := by decide +kernel
theorem eval_atom0034 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0034 = (quadB (outer g) ![1,2,2] * g 5 * g 6) := by
  rw [atom0034_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0034_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90171648 : Int) atom0034) := by
  rw [SparsePolynomial.eval_scale, eval_atom0034]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0035 : SparsePolynomial.Poly := [([0,5,7], -4), ([1,5,7], -8), ([2,5,7], -16), ([3,5,7], -16), ([4,5,7], -16), ([5,5,7], -16), ([5,6,7], -16), ([5,7,7], -16), ([5,7,8], -16), ([5,7,9], -16), ([5,7,10], -16), ([5,7,11], -16), ([5,7,12], -8), ([5,7,14], 8), ([5,7,15], 12), ([5,7,16], 16), ([5,7,17], 18)]
theorem atom0035_data : atom0035 = SparsePolynomial.monoTimes [5,7] 1 base07 := by decide +kernel
theorem eval_atom0035 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0035 = (quadB (outer g) ![1,2,2] * g 5 * g 7) := by
  rw [atom0035_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0035_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (85822200 : Int) atom0035) := by
  rw [SparsePolynomial.eval_scale, eval_atom0035]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0036 : SparsePolynomial.Poly := [([0,5,8], -4), ([1,5,8], -8), ([2,5,8], -16), ([3,5,8], -16), ([4,5,8], -16), ([5,5,8], -16), ([5,6,8], -16), ([5,7,8], -16), ([5,8,8], -16), ([5,8,9], -16), ([5,8,10], -16), ([5,8,11], -16), ([5,8,12], -8), ([5,8,14], 8), ([5,8,15], 12), ([5,8,16], 16), ([5,8,17], 18)]
theorem atom0036_data : atom0036 = SparsePolynomial.monoTimes [5,8] 1 base07 := by decide +kernel
theorem eval_atom0036 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0036 = (quadB (outer g) ![1,2,2] * g 5 * g 8) := by
  rw [atom0036_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0036_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (72822360 : Int) atom0036) := by
  rw [SparsePolynomial.eval_scale, eval_atom0036]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0037 : SparsePolynomial.Poly := [([0,5,9], -4), ([1,5,9], -8), ([2,5,9], -16), ([3,5,9], -16), ([4,5,9], -16), ([5,5,9], -16), ([5,6,9], -16), ([5,7,9], -16), ([5,8,9], -16), ([5,9,9], -16), ([5,9,10], -16), ([5,9,11], -16), ([5,9,12], -8), ([5,9,14], 8), ([5,9,15], 12), ([5,9,16], 16), ([5,9,17], 18)]
theorem atom0037_data : atom0037 = SparsePolynomial.monoTimes [5,9] 1 base07 := by decide +kernel
theorem eval_atom0037 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0037 = (quadB (outer g) ![1,2,2] * g 5 * g 9) := by
  rw [atom0037_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0037_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60242520 : Int) atom0037) := by
  rw [SparsePolynomial.eval_scale, eval_atom0037]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0038 : SparsePolynomial.Poly := [([0,5,10], -4), ([1,5,10], -8), ([2,5,10], -16), ([3,5,10], -16), ([4,5,10], -16), ([5,5,10], -16), ([5,6,10], -16), ([5,7,10], -16), ([5,8,10], -16), ([5,9,10], -16), ([5,10,10], -16), ([5,10,11], -16), ([5,10,12], -8), ([5,10,14], 8), ([5,10,15], 12), ([5,10,16], 16), ([5,10,17], 18)]
theorem atom0038_data : atom0038 = SparsePolynomial.monoTimes [5,10] 1 base07 := by decide +kernel
theorem eval_atom0038 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0038 = (quadB (outer g) ![1,2,2] * g 5 * g 10) := by
  rw [atom0038_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0038_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (51009240 : Int) atom0038) := by
  rw [SparsePolynomial.eval_scale, eval_atom0038]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0039 : SparsePolynomial.Poly := [([0,5,11], -4), ([1,5,11], -8), ([2,5,11], -16), ([3,5,11], -16), ([4,5,11], -16), ([5,5,11], -16), ([5,6,11], -16), ([5,7,11], -16), ([5,8,11], -16), ([5,9,11], -16), ([5,10,11], -16), ([5,11,11], -16), ([5,11,12], -8), ([5,11,14], 8), ([5,11,15], 12), ([5,11,16], 16), ([5,11,17], 18)]
theorem atom0039_data : atom0039 = SparsePolynomial.monoTimes [5,11] 1 base07 := by decide +kernel
theorem eval_atom0039 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0039 = (quadB (outer g) ![1,2,2] * g 5 * g 11) := by
  rw [atom0039_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0039_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46429560 : Int) atom0039) := by
  rw [SparsePolynomial.eval_scale, eval_atom0039]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0040 : SparsePolynomial.Poly := [([0,5,13], -4), ([1,5,13], -8), ([2,5,13], -16), ([3,5,13], -16), ([4,5,13], -16), ([5,5,13], -16), ([5,6,13], -16), ([5,7,13], -16), ([5,8,13], -16), ([5,9,13], -16), ([5,10,13], -16), ([5,11,13], -16), ([5,12,13], -8), ([5,13,14], 8), ([5,13,15], 12), ([5,13,16], 16), ([5,13,17], 18)]
theorem atom0040_data : atom0040 = SparsePolynomial.monoTimes [5,13] 1 base07 := by decide +kernel
theorem eval_atom0040 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0040 = (quadB (outer g) ![1,2,2] * g 5 * g 13) := by
  rw [atom0040_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0040_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68360715 : Int) atom0040) := by
  rw [SparsePolynomial.eval_scale, eval_atom0040]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0041 : SparsePolynomial.Poly := [([0,5,15], -4), ([1,5,15], -8), ([2,5,15], -16), ([3,5,15], -16), ([4,5,15], -16), ([5,5,15], -16), ([5,6,15], -16), ([5,7,15], -16), ([5,8,15], -16), ([5,9,15], -16), ([5,10,15], -16), ([5,11,15], -16), ([5,12,15], -8), ([5,14,15], 8), ([5,15,15], 12), ([5,15,16], 16), ([5,15,17], 18)]
theorem atom0041_data : atom0041 = SparsePolynomial.monoTimes [5,15] 1 base07 := by decide +kernel
theorem eval_atom0041 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0041 = (quadB (outer g) ![1,2,2] * g 5 * g 15) := by
  rw [atom0041_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0041_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (128673585 : Int) atom0041) := by
  rw [SparsePolynomial.eval_scale, eval_atom0041]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0042 : SparsePolynomial.Poly := [([0,5,16], -4), ([1,5,16], -8), ([2,5,16], -16), ([3,5,16], -16), ([4,5,16], -16), ([5,5,16], -16), ([5,6,16], -16), ([5,7,16], -16), ([5,8,16], -16), ([5,9,16], -16), ([5,10,16], -16), ([5,11,16], -16), ([5,12,16], -8), ([5,14,16], 8), ([5,15,16], 12), ([5,16,16], 16), ([5,16,17], 18)]
theorem atom0042_data : atom0042 = SparsePolynomial.monoTimes [5,16] 1 base07 := by decide +kernel
theorem eval_atom0042 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0042 = (quadB (outer g) ![1,2,2] * g 5 * g 16) := by
  rw [atom0042_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0042_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (219814845 : Int) atom0042) := by
  rw [SparsePolynomial.eval_scale, eval_atom0042]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0043 : SparsePolynomial.Poly := [([0,5,17], -4), ([1,5,17], -8), ([2,5,17], -16), ([3,5,17], -16), ([4,5,17], -16), ([5,5,17], -16), ([5,6,17], -16), ([5,7,17], -16), ([5,8,17], -16), ([5,9,17], -16), ([5,10,17], -16), ([5,11,17], -16), ([5,12,17], -8), ([5,14,17], 8), ([5,15,17], 12), ([5,16,17], 16), ([5,17,17], 18)]
theorem atom0043_data : atom0043 = SparsePolynomial.monoTimes [5,17] 1 base07 := by decide +kernel
theorem eval_atom0043 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0043 = (quadB (outer g) ![1,2,2] * g 5 * g 17) := by
  rw [atom0043_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0043_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (214574265 : Int) atom0043) := by
  rw [SparsePolynomial.eval_scale, eval_atom0043]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0044 : SparsePolynomial.Poly := [([0,6,7], -4), ([1,6,7], -8), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -16), ([6,7,10], -16), ([6,7,11], -16), ([6,7,12], -8), ([6,7,14], 8), ([6,7,15], 12), ([6,7,16], 16), ([6,7,17], 18)]
theorem atom0044_data : atom0044 = SparsePolynomial.monoTimes [6,7] 1 base07 := by decide +kernel
theorem eval_atom0044 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0044 = (quadB (outer g) ![1,2,2] * g 6 * g 7) := by
  rw [atom0044_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0044_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23254308 : Int) atom0044) := by
  rw [SparsePolynomial.eval_scale, eval_atom0044]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0045 : SparsePolynomial.Poly := [([0,6,8], -4), ([1,6,8], -8), ([2,6,8], -16), ([3,6,8], -16), ([4,6,8], -16), ([5,6,8], -16), ([6,6,8], -16), ([6,7,8], -16), ([6,8,8], -16), ([6,8,9], -16), ([6,8,10], -16), ([6,8,11], -16), ([6,8,12], -8), ([6,8,14], 8), ([6,8,15], 12), ([6,8,16], 16), ([6,8,17], 18)]
theorem atom0045_data : atom0045 = SparsePolynomial.monoTimes [6,8] 1 base07 := by decide +kernel
theorem eval_atom0045 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0045 = (quadB (outer g) ![1,2,2] * g 6 * g 8) := by
  rw [atom0045_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0045_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (153341400 : Int) atom0045) := by
  rw [SparsePolynomial.eval_scale, eval_atom0045]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0046 : SparsePolynomial.Poly := [([0,6,9], -4), ([1,6,9], -8), ([2,6,9], -16), ([3,6,9], -16), ([4,6,9], -16), ([5,6,9], -16), ([6,6,9], -16), ([6,7,9], -16), ([6,8,9], -16), ([6,9,9], -16), ([6,9,10], -16), ([6,9,11], -16), ([6,9,12], -8), ([6,9,14], 8), ([6,9,15], 12), ([6,9,16], 16), ([6,9,17], 18)]
theorem atom0046_data : atom0046 = SparsePolynomial.monoTimes [6,9] 1 base07 := by decide +kernel
theorem eval_atom0046 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0046 = (quadB (outer g) ![1,2,2] * g 6 * g 9) := by
  rw [atom0046_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0046_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (131729880 : Int) atom0046) := by
  rw [SparsePolynomial.eval_scale, eval_atom0046]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0047 : SparsePolynomial.Poly := [([0,6,10], -4), ([1,6,10], -8), ([2,6,10], -16), ([3,6,10], -16), ([4,6,10], -16), ([5,6,10], -16), ([6,6,10], -16), ([6,7,10], -16), ([6,8,10], -16), ([6,9,10], -16), ([6,10,10], -16), ([6,10,11], -16), ([6,10,12], -8), ([6,10,14], 8), ([6,10,15], 12), ([6,10,16], 16), ([6,10,17], 18)]
theorem atom0047_data : atom0047 = SparsePolynomial.monoTimes [6,10] 1 base07 := by decide +kernel
theorem eval_atom0047 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0047 = (quadB (outer g) ![1,2,2] * g 6 * g 10) := by
  rw [atom0047_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0047_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (110118360 : Int) atom0047) := by
  rw [SparsePolynomial.eval_scale, eval_atom0047]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0048 : SparsePolynomial.Poly := [([0,6,11], -4), ([1,6,11], -8), ([2,6,11], -16), ([3,6,11], -16), ([4,6,11], -16), ([5,6,11], -16), ([6,6,11], -16), ([6,7,11], -16), ([6,8,11], -16), ([6,9,11], -16), ([6,10,11], -16), ([6,11,11], -16), ([6,11,12], -8), ([6,11,14], 8), ([6,11,15], 12), ([6,11,16], 16), ([6,11,17], 18)]
theorem atom0048_data : atom0048 = SparsePolynomial.monoTimes [6,11] 1 base07 := by decide +kernel
theorem eval_atom0048 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0048 = (quadB (outer g) ![1,2,2] * g 6 * g 11) := by
  rw [atom0048_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0048_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (93160440 : Int) atom0048) := by
  rw [SparsePolynomial.eval_scale, eval_atom0048]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0049 : SparsePolynomial.Poly := [([0,6,13], -4), ([1,6,13], -8), ([2,6,13], -16), ([3,6,13], -16), ([4,6,13], -16), ([5,6,13], -16), ([6,6,13], -16), ([6,7,13], -16), ([6,8,13], -16), ([6,9,13], -16), ([6,10,13], -16), ([6,11,13], -16), ([6,12,13], -8), ([6,13,14], 8), ([6,13,15], 12), ([6,13,16], 16), ([6,13,17], 18)]
theorem atom0049_data : atom0049 = SparsePolynomial.monoTimes [6,13] 1 base07 := by decide +kernel
theorem eval_atom0049 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0049 = (quadB (outer g) ![1,2,2] * g 6 * g 13) := by
  rw [atom0049_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0049_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (95732955 : Int) atom0049) := by
  rw [SparsePolynomial.eval_scale, eval_atom0049]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0050 : SparsePolynomial.Poly := [([0,6,15], -4), ([1,6,15], -8), ([2,6,15], -16), ([3,6,15], -16), ([4,6,15], -16), ([5,6,15], -16), ([6,6,15], -16), ([6,7,15], -16), ([6,8,15], -16), ([6,9,15], -16), ([6,10,15], -16), ([6,11,15], -16), ([6,12,15], -8), ([6,14,15], 8), ([6,15,15], 12), ([6,15,16], 16), ([6,15,17], 18)]
theorem atom0050_data : atom0050 = SparsePolynomial.monoTimes [6,15] 1 base07 := by decide +kernel
theorem eval_atom0050 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0050 = (quadB (outer g) ![1,2,2] * g 6 * g 15) := by
  rw [atom0050_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0050_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (142085025 : Int) atom0050) := by
  rw [SparsePolynomial.eval_scale, eval_atom0050]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0051 : SparsePolynomial.Poly := [([0,6,16], -4), ([1,6,16], -8), ([2,6,16], -16), ([3,6,16], -16), ([4,6,16], -16), ([5,6,16], -16), ([6,6,16], -16), ([6,7,16], -16), ([6,8,16], -16), ([6,9,16], -16), ([6,10,16], -16), ([6,11,16], -16), ([6,12,16], -8), ([6,14,16], 8), ([6,15,16], 12), ([6,16,16], 16), ([6,16,17], 18)]
theorem atom0051_data : atom0051 = SparsePolynomial.monoTimes [6,16] 1 base07 := by decide +kernel
theorem eval_atom0051 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0051 = (quadB (outer g) ![1,2,2] * g 6 * g 16) := by
  rw [atom0051_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0051_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (290895525 : Int) atom0051) := by
  rw [SparsePolynomial.eval_scale, eval_atom0051]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0052 : SparsePolynomial.Poly := [([0,6,17], -4), ([1,6,17], -8), ([2,6,17], -16), ([3,6,17], -16), ([4,6,17], -16), ([5,6,17], -16), ([6,6,17], -16), ([6,7,17], -16), ([6,8,17], -16), ([6,9,17], -16), ([6,10,17], -16), ([6,11,17], -16), ([6,12,17], -8), ([6,14,17], 8), ([6,15,17], 12), ([6,16,17], 16), ([6,17,17], 18)]
theorem atom0052_data : atom0052 = SparsePolynomial.monoTimes [6,17] 1 base07 := by decide +kernel
theorem eval_atom0052 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0052 = (quadB (outer g) ![1,2,2] * g 6 * g 17) := by
  rw [atom0052_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0052_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (217623465 : Int) atom0052) := by
  rw [SparsePolynomial.eval_scale, eval_atom0052]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 6 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0053 : SparsePolynomial.Poly := [([0,7,8], -4), ([1,7,8], -8), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -16), ([7,8,10], -16), ([7,8,11], -16), ([7,8,12], -8), ([7,8,14], 8), ([7,8,15], 12), ([7,8,16], 16), ([7,8,17], 18)]
theorem atom0053_data : atom0053 = SparsePolynomial.monoTimes [7,8] 1 base07 := by decide +kernel
theorem eval_atom0053 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0053 = (quadB (outer g) ![1,2,2] * g 7 * g 8) := by
  rw [atom0053_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0053_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90171648 : Int) atom0053) := by
  rw [SparsePolynomial.eval_scale, eval_atom0053]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0054 : SparsePolynomial.Poly := [([0,7,9], -4), ([1,7,9], -8), ([2,7,9], -16), ([3,7,9], -16), ([4,7,9], -16), ([5,7,9], -16), ([6,7,9], -16), ([7,7,9], -16), ([7,8,9], -16), ([7,9,9], -16), ([7,9,10], -16), ([7,9,11], -16), ([7,9,12], -8), ([7,9,14], 8), ([7,9,15], 12), ([7,9,16], 16), ([7,9,17], 18)]
theorem atom0054_data : atom0054 = SparsePolynomial.monoTimes [7,9] 1 base07 := by decide +kernel
theorem eval_atom0054 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0054 = (quadB (outer g) ![1,2,2] * g 7 * g 9) := by
  rw [atom0054_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0054_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (188799600 : Int) atom0054) := by
  rw [SparsePolynomial.eval_scale, eval_atom0054]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0055 : SparsePolynomial.Poly := [([0,7,10], -4), ([1,7,10], -8), ([2,7,10], -16), ([3,7,10], -16), ([4,7,10], -16), ([5,7,10], -16), ([6,7,10], -16), ([7,7,10], -16), ([7,8,10], -16), ([7,9,10], -16), ([7,10,10], -16), ([7,10,11], -16), ([7,10,12], -8), ([7,10,14], 8), ([7,10,15], 12), ([7,10,16], 16), ([7,10,17], 18)]
theorem atom0055_data : atom0055 = SparsePolynomial.monoTimes [7,10] 1 base07 := by decide +kernel
theorem eval_atom0055 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0055 = (quadB (outer g) ![1,2,2] * g 7 * g 10) := by
  rw [atom0055_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0055_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (151664880 : Int) atom0055) := by
  rw [SparsePolynomial.eval_scale, eval_atom0055]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0056 : SparsePolynomial.Poly := [([0,7,11], -4), ([1,7,11], -8), ([2,7,11], -16), ([3,7,11], -16), ([4,7,11], -16), ([5,7,11], -16), ([6,7,11], -16), ([7,7,11], -16), ([7,8,11], -16), ([7,9,11], -16), ([7,10,11], -16), ([7,11,11], -16), ([7,11,12], -8), ([7,11,14], 8), ([7,11,15], 12), ([7,11,16], 16), ([7,11,17], 18)]
theorem atom0056_data : atom0056 = SparsePolynomial.monoTimes [7,11] 1 base07 := by decide +kernel
theorem eval_atom0056 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0056 = (quadB (outer g) ![1,2,2] * g 7 * g 11) := by
  rw [atom0056_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0056_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (119183760 : Int) atom0056) := by
  rw [SparsePolynomial.eval_scale, eval_atom0056]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0057 : SparsePolynomial.Poly := [([0,7,13], -4), ([1,7,13], -8), ([2,7,13], -16), ([3,7,13], -16), ([4,7,13], -16), ([5,7,13], -16), ([6,7,13], -16), ([7,7,13], -16), ([7,8,13], -16), ([7,9,13], -16), ([7,10,13], -16), ([7,11,13], -16), ([7,12,13], -8), ([7,13,14], 8), ([7,13,15], 12), ([7,13,16], 16), ([7,13,17], 18)]
theorem atom0057_data : atom0057 = SparsePolynomial.monoTimes [7,13] 1 base07 := by decide +kernel
theorem eval_atom0057 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0057 = (quadB (outer g) ![1,2,2] * g 7 * g 13) := by
  rw [atom0057_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0057_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (101816730 : Int) atom0057) := by
  rw [SparsePolynomial.eval_scale, eval_atom0057]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0058 : SparsePolynomial.Poly := [([0,7,15], -4), ([1,7,15], -8), ([2,7,15], -16), ([3,7,15], -16), ([4,7,15], -16), ([5,7,15], -16), ([6,7,15], -16), ([7,7,15], -16), ([7,8,15], -16), ([7,9,15], -16), ([7,10,15], -16), ([7,11,15], -16), ([7,12,15], -8), ([7,14,15], 8), ([7,15,15], 12), ([7,15,16], 16), ([7,15,17], 18)]
theorem atom0058_data : atom0058 = SparsePolynomial.monoTimes [7,15] 1 base07 := by decide +kernel
theorem eval_atom0058 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0058 = (quadB (outer g) ![1,2,2] * g 7 * g 15) := by
  rw [atom0058_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0058_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (139336110 : Int) atom0058) := by
  rw [SparsePolynomial.eval_scale, eval_atom0058]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0059 : SparsePolynomial.Poly := [([0,7,16], -4), ([1,7,16], -8), ([2,7,16], -16), ([3,7,16], -16), ([4,7,16], -16), ([5,7,16], -16), ([6,7,16], -16), ([7,7,16], -16), ([7,8,16], -16), ([7,9,16], -16), ([7,10,16], -16), ([7,11,16], -16), ([7,12,16], -8), ([7,14,16], 8), ([7,15,16], 12), ([7,16,16], 16), ([7,16,17], 18)]
theorem atom0059_data : atom0059 = SparsePolynomial.monoTimes [7,16] 1 base07 := by decide +kernel
theorem eval_atom0059 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0059 = (quadB (outer g) ![1,2,2] * g 7 * g 16) := by
  rw [atom0059_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0059_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (287432550 : Int) atom0059) := by
  rw [SparsePolynomial.eval_scale, eval_atom0059]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0060 : SparsePolynomial.Poly := [([0,7,17], -4), ([1,7,17], -8), ([2,7,17], -16), ([3,7,17], -16), ([4,7,17], -16), ([5,7,17], -16), ([6,7,17], -16), ([7,7,17], -16), ([7,8,17], -16), ([7,9,17], -16), ([7,10,17], -16), ([7,11,17], -16), ([7,12,17], -8), ([7,14,17], 8), ([7,15,17], 12), ([7,16,17], 16), ([7,17,17], 18)]
theorem atom0060_data : atom0060 = SparsePolynomial.monoTimes [7,17] 1 base07 := by decide +kernel
theorem eval_atom0060 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0060 = (quadB (outer g) ![1,2,2] * g 7 * g 17) := by
  rw [atom0060_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0060_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (213446430 : Int) atom0060) := by
  rw [SparsePolynomial.eval_scale, eval_atom0060]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 7 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0061 : SparsePolynomial.Poly := [([0,8,9], -4), ([1,8,9], -8), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -16), ([8,9,10], -16), ([8,9,11], -16), ([8,9,12], -8), ([8,9,14], 8), ([8,9,15], 12), ([8,9,16], 16), ([8,9,17], 18)]
theorem atom0061_data : atom0061 = SparsePolynomial.monoTimes [8,9] 1 base07 := by decide +kernel
theorem eval_atom0061 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0061 = (quadB (outer g) ![1,2,2] * g 8 * g 9) := by
  rw [atom0061_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0061_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (63799680 : Int) atom0061) := by
  rw [SparsePolynomial.eval_scale, eval_atom0061]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0062 : SparsePolynomial.Poly := [([0,8,10], -4), ([1,8,10], -8), ([2,8,10], -16), ([3,8,10], -16), ([4,8,10], -16), ([5,8,10], -16), ([6,8,10], -16), ([7,8,10], -16), ([8,8,10], -16), ([8,9,10], -16), ([8,10,10], -16), ([8,10,11], -16), ([8,10,12], -8), ([8,10,14], 8), ([8,10,15], 12), ([8,10,16], 16), ([8,10,17], 18)]
theorem atom0062_data : atom0062 = SparsePolynomial.monoTimes [8,10] 1 base07 := by decide +kernel
theorem eval_atom0062 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0062 = (quadB (outer g) ![1,2,2] * g 8 * g 10) := by
  rw [atom0062_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0062_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (185764032 : Int) atom0062) := by
  rw [SparsePolynomial.eval_scale, eval_atom0062]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0063 : SparsePolynomial.Poly := [([0,8,11], -4), ([1,8,11], -8), ([2,8,11], -16), ([3,8,11], -16), ([4,8,11], -16), ([5,8,11], -16), ([6,8,11], -16), ([7,8,11], -16), ([8,8,11], -16), ([8,9,11], -16), ([8,10,11], -16), ([8,11,11], -16), ([8,11,12], -8), ([8,11,14], 8), ([8,11,15], 12), ([8,11,16], 16), ([8,11,17], 18)]
theorem atom0063_data : atom0063 = SparsePolynomial.monoTimes [8,11] 1 base07 := by decide +kernel
theorem eval_atom0063 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0063 = (quadB (outer g) ![1,2,2] * g 8 * g 11) := by
  rw [atom0063_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0063_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (145341120 : Int) atom0063) := by
  rw [SparsePolynomial.eval_scale, eval_atom0063]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0064 : SparsePolynomial.Poly := [([0,8,13], -4), ([1,8,13], -8), ([2,8,13], -16), ([3,8,13], -16), ([4,8,13], -16), ([5,8,13], -16), ([6,8,13], -16), ([7,8,13], -16), ([8,8,13], -16), ([8,9,13], -16), ([8,10,13], -16), ([8,11,13], -16), ([8,12,13], -8), ([8,13,14], 8), ([8,13,15], 12), ([8,13,16], 16), ([8,13,17], 18)]
theorem atom0064_data : atom0064 = SparsePolynomial.monoTimes [8,13] 1 base07 := by decide +kernel
theorem eval_atom0064 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0064 = (quadB (outer g) ![1,2,2] * g 8 * g 13) := by
  rw [atom0064_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0064_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (97236480 : Int) atom0064) := by
  rw [SparsePolynomial.eval_scale, eval_atom0064]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0065 : SparsePolynomial.Poly := [([0,8,15], -4), ([1,8,15], -8), ([2,8,15], -16), ([3,8,15], -16), ([4,8,15], -16), ([5,8,15], -16), ([6,8,15], -16), ([7,8,15], -16), ([8,8,15], -16), ([8,9,15], -16), ([8,10,15], -16), ([8,11,15], -16), ([8,12,15], -8), ([8,14,15], 8), ([8,15,15], 12), ([8,15,16], 16), ([8,15,17], 18)]
theorem atom0065_data : atom0065 = SparsePolynomial.monoTimes [8,15] 1 base07 := by decide +kernel
theorem eval_atom0065 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0065 = (quadB (outer g) ![1,2,2] * g 8 * g 15) := by
  rw [atom0065_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0065_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (110616960 : Int) atom0065) := by
  rw [SparsePolynomial.eval_scale, eval_atom0065]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0066 : SparsePolynomial.Poly := [([0,8,16], -4), ([1,8,16], -8), ([2,8,16], -16), ([3,8,16], -16), ([4,8,16], -16), ([5,8,16], -16), ([6,8,16], -16), ([7,8,16], -16), ([8,8,16], -16), ([8,9,16], -16), ([8,10,16], -16), ([8,11,16], -16), ([8,12,16], -8), ([8,14,16], 8), ([8,15,16], 12), ([8,16,16], 16), ([8,16,17], 18)]
theorem atom0066_data : atom0066 = SparsePolynomial.monoTimes [8,16] 1 base07 := by decide +kernel
theorem eval_atom0066 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0066 = (quadB (outer g) ![1,2,2] * g 8 * g 16) := by
  rw [atom0066_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0066_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (255247680 : Int) atom0066) := by
  rw [SparsePolynomial.eval_scale, eval_atom0066]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0067 : SparsePolynomial.Poly := [([0,8,17], -4), ([1,8,17], -8), ([2,8,17], -16), ([3,8,17], -16), ([4,8,17], -16), ([5,8,17], -16), ([6,8,17], -16), ([7,8,17], -16), ([8,8,17], -16), ([8,9,17], -16), ([8,10,17], -16), ([8,11,17], -16), ([8,12,17], -8), ([8,14,17], 8), ([8,15,17], 12), ([8,16,17], 16), ([8,17,17], 18)]
theorem atom0067_data : atom0067 = SparsePolynomial.monoTimes [8,17] 1 base07 := by decide +kernel
theorem eval_atom0067 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0067 = (quadB (outer g) ![1,2,2] * g 8 * g 17) := by
  rw [atom0067_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0067_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (171391680 : Int) atom0067) := by
  rw [SparsePolynomial.eval_scale, eval_atom0067]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 8 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0068 : SparsePolynomial.Poly := [([0,9,10], -4), ([1,9,10], -8), ([2,9,10], -16), ([3,9,10], -16), ([4,9,10], -16), ([5,9,10], -16), ([6,9,10], -16), ([7,9,10], -16), ([8,9,10], -16), ([9,9,10], -16), ([9,10,10], -16), ([9,10,11], -16), ([9,10,12], -8), ([9,10,14], 8), ([9,10,15], 12), ([9,10,16], 16), ([9,10,17], 18)]
theorem atom0068_data : atom0068 = SparsePolynomial.monoTimes [9,10] 1 base07 := by decide +kernel
theorem eval_atom0068 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0068 = (quadB (outer g) ![1,2,2] * g 9 * g 10) := by
  rw [atom0068_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0068_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48652800 : Int) atom0068) := by
  rw [SparsePolynomial.eval_scale, eval_atom0068]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0069 : SparsePolynomial.Poly := [([0,9,11], -4), ([1,9,11], -8), ([2,9,11], -16), ([3,9,11], -16), ([4,9,11], -16), ([5,9,11], -16), ([6,9,11], -16), ([7,9,11], -16), ([8,9,11], -16), ([9,9,11], -16), ([9,10,11], -16), ([9,11,11], -16), ([9,11,12], -8), ([9,11,14], 8), ([9,11,15], 12), ([9,11,16], 16), ([9,11,17], 18)]
theorem atom0069_data : atom0069 = SparsePolynomial.monoTimes [9,11] 1 base07 := by decide +kernel
theorem eval_atom0069 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0069 = (quadB (outer g) ![1,2,2] * g 9 * g 11) := by
  rw [atom0069_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0069_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (132585600 : Int) atom0069) := by
  rw [SparsePolynomial.eval_scale, eval_atom0069]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0070 : SparsePolynomial.Poly := [([0,9,12], -4), ([1,9,12], -8), ([2,9,12], -16), ([3,9,12], -16), ([4,9,12], -16), ([5,9,12], -16), ([6,9,12], -16), ([7,9,12], -16), ([8,9,12], -16), ([9,9,12], -16), ([9,10,12], -16), ([9,11,12], -16), ([9,12,12], -8), ([9,12,14], 8), ([9,12,15], 12), ([9,12,16], 16), ([9,12,17], 18)]
theorem atom0070_data : atom0070 = SparsePolynomial.monoTimes [9,12] 1 base07 := by decide +kernel
theorem eval_atom0070 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0070 = (quadB (outer g) ![1,2,2] * g 9 * g 12) := by
  rw [atom0070_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0070_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13571460 : Int) atom0070) := by
  rw [SparsePolynomial.eval_scale, eval_atom0070]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0071 : SparsePolynomial.Poly := [([0,9,13], -4), ([1,9,13], -8), ([2,9,13], -16), ([3,9,13], -16), ([4,9,13], -16), ([5,9,13], -16), ([6,9,13], -16), ([7,9,13], -16), ([8,9,13], -16), ([9,9,13], -16), ([9,10,13], -16), ([9,11,13], -16), ([9,12,13], -8), ([9,13,14], 8), ([9,13,15], 12), ([9,13,16], 16), ([9,13,17], 18)]
theorem atom0071_data : atom0071 = SparsePolynomial.monoTimes [9,13] 1 base07 := by decide +kernel
theorem eval_atom0071 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0071 = (quadB (outer g) ![1,2,2] * g 9 * g 13) := by
  rw [atom0071_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0071_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91971660 : Int) atom0071) := by
  rw [SparsePolynomial.eval_scale, eval_atom0071]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0072 : SparsePolynomial.Poly := [([0,9,15], -4), ([1,9,15], -8), ([2,9,15], -16), ([3,9,15], -16), ([4,9,15], -16), ([5,9,15], -16), ([6,9,15], -16), ([7,9,15], -16), ([8,9,15], -16), ([9,9,15], -16), ([9,10,15], -16), ([9,11,15], -16), ([9,12,15], -8), ([9,14,15], 8), ([9,15,15], 12), ([9,15,16], 16), ([9,15,17], 18)]
theorem atom0072_data : atom0072 = SparsePolynomial.monoTimes [9,15] 1 base07 := by decide +kernel
theorem eval_atom0072 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0072 = (quadB (outer g) ![1,2,2] * g 9 * g 15) := by
  rw [atom0072_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0072_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (70656420 : Int) atom0072) := by
  rw [SparsePolynomial.eval_scale, eval_atom0072]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0073 : SparsePolynomial.Poly := [([0,9,16], -4), ([1,9,16], -8), ([2,9,16], -16), ([3,9,16], -16), ([4,9,16], -16), ([5,9,16], -16), ([6,9,16], -16), ([7,9,16], -16), ([8,9,16], -16), ([9,9,16], -16), ([9,10,16], -16), ([9,11,16], -16), ([9,12,16], -8), ([9,14,16], 8), ([9,15,16], 12), ([9,16,16], 16), ([9,16,17], 18)]
theorem atom0073_data : atom0073 = SparsePolynomial.monoTimes [9,16] 1 base07 := by decide +kernel
theorem eval_atom0073 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0073 = (quadB (outer g) ![1,2,2] * g 9 * g 16) := by
  rw [atom0073_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0073_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (198298740 : Int) atom0073) := by
  rw [SparsePolynomial.eval_scale, eval_atom0073]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0074 : SparsePolynomial.Poly := [([0,9,17], -4), ([1,9,17], -8), ([2,9,17], -16), ([3,9,17], -16), ([4,9,17], -16), ([5,9,17], -16), ([6,9,17], -16), ([7,9,17], -16), ([8,9,17], -16), ([9,9,17], -16), ([9,10,17], -16), ([9,11,17], -16), ([9,12,17], -8), ([9,14,17], 8), ([9,15,17], 12), ([9,16,17], 16), ([9,17,17], 18)]
theorem atom0074_data : atom0074 = SparsePolynomial.monoTimes [9,17] 1 base07 := by decide +kernel
theorem eval_atom0074 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0074 = (quadB (outer g) ![1,2,2] * g 9 * g 17) := by
  rw [atom0074_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0074_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (98583300 : Int) atom0074) := by
  rw [SparsePolynomial.eval_scale, eval_atom0074]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0075 : SparsePolynomial.Poly := [([0,10,12], -4), ([1,10,12], -8), ([2,10,12], -16), ([3,10,12], -16), ([4,10,12], -16), ([5,10,12], -16), ([6,10,12], -16), ([7,10,12], -16), ([8,10,12], -16), ([9,10,12], -16), ([10,10,12], -16), ([10,11,12], -16), ([10,12,12], -8), ([10,12,14], 8), ([10,12,15], 12), ([10,12,16], 16), ([10,12,17], 18)]
theorem atom0075_data : atom0075 = SparsePolynomial.monoTimes [10,12] 1 base07 := by decide +kernel
theorem eval_atom0075 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0075 = (quadB (outer g) ![1,2,2] * g 10 * g 12) := by
  rw [atom0075_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0075_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30609180 : Int) atom0075) := by
  rw [SparsePolynomial.eval_scale, eval_atom0075]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0076 : SparsePolynomial.Poly := [([0,10,13], -4), ([1,10,13], -8), ([2,10,13], -16), ([3,10,13], -16), ([4,10,13], -16), ([5,10,13], -16), ([6,10,13], -16), ([7,10,13], -16), ([8,10,13], -16), ([9,10,13], -16), ([10,10,13], -16), ([10,11,13], -16), ([10,12,13], -8), ([10,13,14], 8), ([10,13,15], 12), ([10,13,16], 16), ([10,13,17], 18)]
theorem atom0076_data : atom0076 = SparsePolynomial.monoTimes [10,13] 1 base07 := by decide +kernel
theorem eval_atom0076 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0076 = (quadB (outer g) ![1,2,2] * g 10 * g 13) := by
  rw [atom0076_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0076_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82673940 : Int) atom0076) := by
  rw [SparsePolynomial.eval_scale, eval_atom0076]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0077 : SparsePolynomial.Poly := [([0,10,15], -4), ([1,10,15], -8), ([2,10,15], -16), ([3,10,15], -16), ([4,10,15], -16), ([5,10,15], -16), ([6,10,15], -16), ([7,10,15], -16), ([8,10,15], -16), ([9,10,15], -16), ([10,10,15], -16), ([10,11,15], -16), ([10,12,15], -8), ([10,14,15], 8), ([10,15,15], 12), ([10,15,16], 16), ([10,15,17], 18)]
theorem atom0077_data : atom0077 = SparsePolynomial.monoTimes [10,15] 1 base07 := by decide +kernel
theorem eval_atom0077 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0077 = (quadB (outer g) ![1,2,2] * g 10 * g 15) := by
  rw [atom0077_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0077_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7310460 : Int) atom0077) := by
  rw [SparsePolynomial.eval_scale, eval_atom0077]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0078 : SparsePolynomial.Poly := [([0,10,16], -4), ([1,10,16], -8), ([2,10,16], -16), ([3,10,16], -16), ([4,10,16], -16), ([5,10,16], -16), ([6,10,16], -16), ([7,10,16], -16), ([8,10,16], -16), ([9,10,16], -16), ([10,10,16], -16), ([10,11,16], -16), ([10,12,16], -8), ([10,14,16], 8), ([10,15,16], 12), ([10,16,16], 16), ([10,16,17], 18)]
theorem atom0078_data : atom0078 = SparsePolynomial.monoTimes [10,16] 1 base07 := by decide +kernel
theorem eval_atom0078 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0078 = (quadB (outer g) ![1,2,2] * g 10 * g 16) := by
  rw [atom0078_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0078_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (109255980 : Int) atom0078) := by
  rw [SparsePolynomial.eval_scale, eval_atom0078]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0079 : SparsePolynomial.Poly := [([0,11,12], -4), ([1,11,12], -8), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -8), ([11,12,14], 8), ([11,12,15], 12), ([11,12,16], 16), ([11,12,17], 18)]
theorem atom0079_data : atom0079 = SparsePolynomial.monoTimes [11,12] 1 base07 := by decide +kernel
theorem eval_atom0079 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0079 = (quadB (outer g) ![1,2,2] * g 11 * g 12) := by
  rw [atom0079_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0079_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30159360 : Int) atom0079) := by
  rw [SparsePolynomial.eval_scale, eval_atom0079]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0080 : SparsePolynomial.Poly := [([0,11,13], -4), ([1,11,13], -8), ([2,11,13], -16), ([3,11,13], -16), ([4,11,13], -16), ([5,11,13], -16), ([6,11,13], -16), ([7,11,13], -16), ([8,11,13], -16), ([9,11,13], -16), ([10,11,13], -16), ([11,11,13], -16), ([11,12,13], -8), ([11,13,14], 8), ([11,13,15], 12), ([11,13,16], 16), ([11,13,17], 18)]
theorem atom0080_data : atom0080 = SparsePolynomial.monoTimes [11,13] 1 base07 := by decide +kernel
theorem eval_atom0080 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0080 = (quadB (outer g) ![1,2,2] * g 11 * g 13) := by
  rw [atom0080_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0080_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (69914880 : Int) atom0080) := by
  rw [SparsePolynomial.eval_scale, eval_atom0080]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0081 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -16), ([0,1,4], -16), ([0,1,5], -16), ([0,1,6], -16), ([0,1,7], -16), ([0,1,8], -16), ([0,1,9], -16), ([0,1,10], -16), ([0,1,11], -16), ([0,1,12], -14), ([0,1,13], -10), ([0,1,14], -2), ([0,1,15], 2), ([0,1,16], 10), ([0,1,17], 18)]
theorem atom0081_data : atom0081 = SparsePolynomial.monoTimes [0,1] 1 base08 := by decide +kernel
theorem eval_atom0081 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0081 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0081_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0081_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28062720 : Int) atom0081) := by
  rw [SparsePolynomial.eval_scale, eval_atom0081]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0082 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -16), ([0,2,4], -16), ([0,2,5], -16), ([0,2,6], -16), ([0,2,7], -16), ([0,2,8], -16), ([0,2,9], -16), ([0,2,10], -16), ([0,2,11], -16), ([0,2,12], -14), ([0,2,13], -10), ([0,2,14], -2), ([0,2,15], 2), ([0,2,16], 10), ([0,2,17], 18)]
theorem atom0082_data : atom0082 = SparsePolynomial.monoTimes [0,2] 1 base08 := by decide +kernel
theorem eval_atom0082 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0082 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0082_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0082_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41045760 : Int) atom0082) := by
  rw [SparsePolynomial.eval_scale, eval_atom0082]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0083 : SparsePolynomial.Poly := [([0,0,3], -8), ([0,1,3], -12), ([0,2,3], -16), ([0,3,3], -16), ([0,3,4], -16), ([0,3,5], -16), ([0,3,6], -16), ([0,3,7], -16), ([0,3,8], -16), ([0,3,9], -16), ([0,3,10], -16), ([0,3,11], -16), ([0,3,12], -14), ([0,3,13], -10), ([0,3,14], -2), ([0,3,15], 2), ([0,3,16], 10), ([0,3,17], 18)]
theorem atom0083_data : atom0083 = SparsePolynomial.monoTimes [0,3] 1 base08 := by decide +kernel
theorem eval_atom0083 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0083 = (quadB (outer g) ![2,2,1] * g 0 * g 3) := by
  rw [atom0083_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0083_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54028800 : Int) atom0083) := by
  rw [SparsePolynomial.eval_scale, eval_atom0083]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0084 : SparsePolynomial.Poly := [([0,0,4], -8), ([0,1,4], -12), ([0,2,4], -16), ([0,3,4], -16), ([0,4,4], -16), ([0,4,5], -16), ([0,4,6], -16), ([0,4,7], -16), ([0,4,8], -16), ([0,4,9], -16), ([0,4,10], -16), ([0,4,11], -16), ([0,4,12], -14), ([0,4,13], -10), ([0,4,14], -2), ([0,4,15], 2), ([0,4,16], 10), ([0,4,17], 18)]
theorem atom0084_data : atom0084 = SparsePolynomial.monoTimes [0,4] 1 base08 := by decide +kernel
theorem eval_atom0084 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0084 = (quadB (outer g) ![2,2,1] * g 0 * g 4) := by
  rw [atom0084_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0084_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (67011840 : Int) atom0084) := by
  rw [SparsePolynomial.eval_scale, eval_atom0084]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0085 : SparsePolynomial.Poly := [([0,0,5], -8), ([0,1,5], -12), ([0,2,5], -16), ([0,3,5], -16), ([0,4,5], -16), ([0,5,5], -16), ([0,5,6], -16), ([0,5,7], -16), ([0,5,8], -16), ([0,5,9], -16), ([0,5,10], -16), ([0,5,11], -16), ([0,5,12], -14), ([0,5,13], -10), ([0,5,14], -2), ([0,5,15], 2), ([0,5,16], 10), ([0,5,17], 18)]
theorem atom0085_data : atom0085 = SparsePolynomial.monoTimes [0,5] 1 base08 := by decide +kernel
theorem eval_atom0085 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0085 = (quadB (outer g) ![2,2,1] * g 0 * g 5) := by
  rw [atom0085_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0085_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (79994880 : Int) atom0085) := by
  rw [SparsePolynomial.eval_scale, eval_atom0085]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0086 : SparsePolynomial.Poly := [([0,0,6], -8), ([0,1,6], -12), ([0,2,6], -16), ([0,3,6], -16), ([0,4,6], -16), ([0,5,6], -16), ([0,6,6], -16), ([0,6,7], -16), ([0,6,8], -16), ([0,6,9], -16), ([0,6,10], -16), ([0,6,11], -16), ([0,6,12], -14), ([0,6,13], -10), ([0,6,14], -2), ([0,6,15], 2), ([0,6,16], 10), ([0,6,17], 18)]
theorem atom0086_data : atom0086 = SparsePolynomial.monoTimes [0,6] 1 base08 := by decide +kernel
theorem eval_atom0086 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0086 = (quadB (outer g) ![2,2,1] * g 0 * g 6) := by
  rw [atom0086_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0086_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (92977920 : Int) atom0086) := by
  rw [SparsePolynomial.eval_scale, eval_atom0086]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0087 : SparsePolynomial.Poly := [([0,0,7], -8), ([0,1,7], -12), ([0,2,7], -16), ([0,3,7], -16), ([0,4,7], -16), ([0,5,7], -16), ([0,6,7], -16), ([0,7,7], -16), ([0,7,8], -16), ([0,7,9], -16), ([0,7,10], -16), ([0,7,11], -16), ([0,7,12], -14), ([0,7,13], -10), ([0,7,14], -2), ([0,7,15], 2), ([0,7,16], 10), ([0,7,17], 18)]
theorem atom0087_data : atom0087 = SparsePolynomial.monoTimes [0,7] 1 base08 := by decide +kernel
theorem eval_atom0087 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0087 = (quadB (outer g) ![2,2,1] * g 0 * g 7) := by
  rw [atom0087_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0087_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105960960 : Int) atom0087) := by
  rw [SparsePolynomial.eval_scale, eval_atom0087]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0088 : SparsePolynomial.Poly := [([0,0,8], -8), ([0,1,8], -12), ([0,2,8], -16), ([0,3,8], -16), ([0,4,8], -16), ([0,5,8], -16), ([0,6,8], -16), ([0,7,8], -16), ([0,8,8], -16), ([0,8,9], -16), ([0,8,10], -16), ([0,8,11], -16), ([0,8,12], -14), ([0,8,13], -10), ([0,8,14], -2), ([0,8,15], 2), ([0,8,16], 10), ([0,8,17], 18)]
theorem atom0088_data : atom0088 = SparsePolynomial.monoTimes [0,8] 1 base08 := by decide +kernel
theorem eval_atom0088 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0088 = (quadB (outer g) ![2,2,1] * g 0 * g 8) := by
  rw [atom0088_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0088_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (112539840 : Int) atom0088) := by
  rw [SparsePolynomial.eval_scale, eval_atom0088]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0089 : SparsePolynomial.Poly := [([0,0,9], -8), ([0,1,9], -12), ([0,2,9], -16), ([0,3,9], -16), ([0,4,9], -16), ([0,5,9], -16), ([0,6,9], -16), ([0,7,9], -16), ([0,8,9], -16), ([0,9,9], -16), ([0,9,10], -16), ([0,9,11], -16), ([0,9,12], -14), ([0,9,13], -10), ([0,9,14], -2), ([0,9,15], 2), ([0,9,16], 10), ([0,9,17], 18)]
theorem atom0089_data : atom0089 = SparsePolynomial.monoTimes [0,9] 1 base08 := by decide +kernel
theorem eval_atom0089 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0089 = (quadB (outer g) ![2,2,1] * g 0 * g 9) := by
  rw [atom0089_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0089_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (126651840 : Int) atom0089) := by
  rw [SparsePolynomial.eval_scale, eval_atom0089]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0090 : SparsePolynomial.Poly := [([0,0,10], -8), ([0,1,10], -12), ([0,2,10], -16), ([0,3,10], -16), ([0,4,10], -16), ([0,5,10], -16), ([0,6,10], -16), ([0,7,10], -16), ([0,8,10], -16), ([0,9,10], -16), ([0,10,10], -16), ([0,10,11], -16), ([0,10,12], -14), ([0,10,13], -10), ([0,10,14], -2), ([0,10,15], 2), ([0,10,16], 10), ([0,10,17], 18)]
theorem atom0090_data : atom0090 = SparsePolynomial.monoTimes [0,10] 1 base08 := by decide +kernel
theorem eval_atom0090 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0090 = (quadB (outer g) ![2,2,1] * g 0 * g 10) := by
  rw [atom0090_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0090_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (137618880 : Int) atom0090) := by
  rw [SparsePolynomial.eval_scale, eval_atom0090]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0091 : SparsePolynomial.Poly := [([0,0,11], -8), ([0,1,11], -12), ([0,2,11], -16), ([0,3,11], -16), ([0,4,11], -16), ([0,5,11], -16), ([0,6,11], -16), ([0,7,11], -16), ([0,8,11], -16), ([0,9,11], -16), ([0,10,11], -16), ([0,11,11], -16), ([0,11,12], -14), ([0,11,13], -10), ([0,11,14], -2), ([0,11,15], 2), ([0,11,16], 10), ([0,11,17], 18)]
theorem atom0091_data : atom0091 = SparsePolynomial.monoTimes [0,11] 1 base08 := by decide +kernel
theorem eval_atom0091 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0091 = (quadB (outer g) ![2,2,1] * g 0 * g 11) := by
  rw [atom0091_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0091_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (157893120 : Int) atom0091) := by
  rw [SparsePolynomial.eval_scale, eval_atom0091]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0092 : SparsePolynomial.Poly := [([0,0,16], -8), ([0,1,16], -12), ([0,2,16], -16), ([0,3,16], -16), ([0,4,16], -16), ([0,5,16], -16), ([0,6,16], -16), ([0,7,16], -16), ([0,8,16], -16), ([0,9,16], -16), ([0,10,16], -16), ([0,11,16], -16), ([0,12,16], -14), ([0,13,16], -10), ([0,14,16], -2), ([0,15,16], 2), ([0,16,16], 10), ([0,16,17], 18)]
theorem atom0092_data : atom0092 = SparsePolynomial.monoTimes [0,16] 1 base08 := by decide +kernel
theorem eval_atom0092 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0092 = (quadB (outer g) ![2,2,1] * g 0 * g 16) := by
  rw [atom0092_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0092_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30885120 : Int) atom0092) := by
  rw [SparsePolynomial.eval_scale, eval_atom0092]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0093 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -16), ([1,1,4], -16), ([1,1,5], -16), ([1,1,6], -16), ([1,1,7], -16), ([1,1,8], -16), ([1,1,9], -16), ([1,1,10], -16), ([1,1,11], -16), ([1,1,12], -14), ([1,1,13], -10), ([1,1,14], -2), ([1,1,15], 2), ([1,1,16], 10), ([1,1,17], 18)]
theorem atom0093_data : atom0093 = SparsePolynomial.monoTimes [1,1] 1 base08 := by decide +kernel
theorem eval_atom0093 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0093 = (quadB (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0093_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0093_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (58044000 : Int) atom0093) := by
  rw [SparsePolynomial.eval_scale, eval_atom0093]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0094 : SparsePolynomial.Poly := [([0,1,17], -8), ([1,1,17], -12), ([1,2,17], -16), ([1,3,17], -16), ([1,4,17], -16), ([1,5,17], -16), ([1,6,17], -16), ([1,7,17], -16), ([1,8,17], -16), ([1,9,17], -16), ([1,10,17], -16), ([1,11,17], -16), ([1,12,17], -14), ([1,13,17], -10), ([1,14,17], -2), ([1,15,17], 2), ([1,16,17], 10), ([1,17,17], 18)]
theorem atom0094_data : atom0094 = SparsePolynomial.monoTimes [1,17] 1 base08 := by decide +kernel
theorem eval_atom0094 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0094 = (quadB (outer g) ![2,2,1] * g 1 * g 17) := by
  rw [atom0094_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0094_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3519600 : Int) atom0094) := by
  rw [SparsePolynomial.eval_scale, eval_atom0094]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def block001 : SparsePolynomial.Poly := [([0,0,0], -120637440), ([0,0,1], -465776640), ([0,0,2], -569640960), ([0,0,3], -673505280), ([0,0,4], -777369600), ([0,0,5], -881233920), ([0,0,6], -985098240), ([0,0,7], -1088962560), ([0,0,8], -1192826880), ([0,0,9], -1296691200), ([0,0,10], -1400555520), ([0,0,11], -1504419840), ([0,0,12], -241274880), ([0,0,13], -241274880), ([0,0,14], -241274880), ([0,0,15], -241274880), ([0,0,16], -247080960), ([0,0,17], -350945280), ([0,1,1], -921742080), ([0,1,2], -1182827520), ([0,1,3], -1338624000), ([0,1,4], -1494420480), ([0,1,5], -1650216960), ([0,1,6], -1806013440), ([0,1,7], -1961809920), ([0,1,8], -2143223040), ([0,1,9], -2294503680), ([0,1,10], -2458364160), ([0,1,11], -2584995840), ([0,1,12], -634152960), ([0,1,13], -521902080), ([0,1,14], -297400320), ([0,1,15], -185149440), ([0,1,16], -89994240), ([0,1,17], 126026880), ([0,2,2], -777369600), ([0,2,3], -1762467840), ([0,2,4], -1970196480), ([0,2,5], -2177925120), ([0,2,6], -2385653760), ([0,2,7], -2593382400), ([0,2,8], -2801111040), ([0,2,9], -3008839680), ([0,2,10], -3216568320), ([0,2,11], -3424296960), ([0,2,12], -815915520), ([0,2,13], -651732480), ([0,2,14], -323366400), ([0,2,15], -159183360), ([0,2,16], -458680320), ([0,2,17], 387878400), ([0,3,3], -985098240), ([0,3,4], -2177925120), ([0,3,5], -2385653760), ([0,3,6], -2593382400), ([0,3,7], -2801111040), ([0,3,8], -3008839680), ([0,3,9], -3216568320), ([0,3,10], -3424296960), ([0,3,11], -3672345600), ([0,3,12], -997678080), ([0,3,13], -878653440), ([0,3,14], -349332480), ([0,3,15], -287078400), ([0,3,16], -580285440), ([0,3,17], 410941440), ([0,4,4], -1192826880), ([0,4,5], -2954068992), ([0,4,6], -2953368480), ([0,4,7], -3037292160), ([0,4,8], -3216568320), ([0,4,9], -3424296960), ([0,4,10], -3632025600), ([0,4,11], -3858368640), ([0,4,12], -1179440640), ([0,4,13], -1054349520), ([0,4,14], -375298560), ([0,4,15], -490827120), ([0,4,16], -482438320), ([0,4,17], 153553680), ([0,5,5], -1400555520), ([0,5,6], -3369526272), ([0,5,7], -3559857120), ([0,5,8], -3715586400), ([0,5,9], -3872995680), ([0,5,10], -4043791200), ([0,5,11], -4233201120), ([0,5,12], -1361203200), ([0,5,13], -1314666540), ([0,5,14], -401264640), ([0,5,15], -595979460), ([0,5,16], -573472500), ([0,5,17], 230665500), ([0,6,6], -1608284160), ([0,6,7], -3517314192), ([0,6,8], -4245391200), ([0,6,9], -4366673760), ([0,6,10], -4487956320), ([0,6,11], -4627853280), ([0,6,12], -1542965760), ([0,6,13], -1553985900), ([0,6,14], -427230720), ([0,6,15], -623659140), ([0,6,16], -727964820), ([0,6,17], 452163420), ([0,7,7], -1816012800), ([0,7,8], -4200440832), ([0,7,9], -4802681280), ([0,7,10], -4861871040), ([0,7,11], -4939675200), ([0,7,12], -1724728320), ([0,7,13], -1708151400), ([0,7,14], -453196800), ([0,7,15], -586697400), ([0,7,16], -584282520), ([0,7,17], 702566280), ([0,8,8], -2023741440), ([0,8,9], -4510410240), ([0,8,10], -5205996288), ([0,8,11], -5252033280), ([0,8,12], -1919299200), ([0,8,13], -1858085760), ([0,8,14], -568821120), ([0,8,15], -561129600), ([0,8,16], -389754240), ([0,8,17], 989205120), ([0,9,9], -2231470080), ([0,9,10], -4865280000), ([0,9,11], -5408739840), ([0,9,12], -2153089680), ([0,9,13], -1960083120), ([0,9,14], -578981760), ([0,9,15], -355000080), ([0,9,16], -20838480), ([0,9,17], 1534454640), ([0,10,10], -2439198720), ([0,10,11], -5086126080), ([0,10,12], -2407035120), ([0,10,13], -2064818640), ([0,10,14], -633171840), ([0,10,15], -111938160), ([0,10,16], 445002960), ([0,10,17], 2126194560), ([0,11,11], -2646927360), ([0,11,12], -2572416000), ([0,11,13], -2099865600), ([0,11,14], -557061120), ([0,11,15], 74511360), ([0,11,16], 1084769280), ([0,11,17], 2491130880), ([0,12,12], -120637440), ([0,12,13], -241274880), ([0,12,14], -241274880), ([0,12,15], -241274880), ([0,12,16], -432391680), ([0,12,17], -350945280), ([0,13,13], -120637440), ([0,13,14], -241274880), ([0,13,15], -241274880), ([0,13,16], -308851200), ([0,13,17], -350945280), ([0,14,14], -120637440), ([0,14,15], -241274880), ([0,14,16], -61770240), ([0,14,17], 482549760), ([0,15,15], -120637440), ([0,15,16], 61770240), ([0,15,17], 482549760), ([0,16,16], 308851200), ([0,16,17], 1389427200), ([0,17,17], 1184440320), ([1,1,1], -696528000), ([1,1,2], -928704000), ([1,1,3], -928704000), ([1,1,4], -928704000), ([1,1,5], -928704000), ([1,1,6], -928704000), ([1,1,7], -928704000), ([1,1,8], -979937280), ([1,1,9], -970905600), ([1,1,10], -987033600), ([1,1,11], -928704000), ([1,1,12], -812616000), ([1,1,13], -580440000), ([1,1,14], -116088000), ([1,1,15], 116088000), ([1,1,16], 580440000), ([1,1,17], 1002556800), ([1,2,8], -102466560), ([1,2,9], -84403200), ([1,2,10], -116659200), ([1,2,16], -749952000), ([1,2,17], -56313600), ([1,3,8], -102466560), ([1,3,9], -84403200), ([1,3,10], -116659200), ([1,3,11], -80640000), ([1,3,13], -194181120), ([1,3,15], -307722240), ([1,3,16], -1252823040), ([1,3,17], -477576960), ([1,4,5], -721373184), ([1,4,6], -304514880), ([1,4,7], -56904960), ([1,4,8], -102466560), ([1,4,9], -84403200), ([1,4,10], -116659200), ([1,4,11], -37228800), ([1,4,13], -285912480), ([1,4,15], -767151840), ([1,4,16], -1316789600), ([1,4,17], -1459741920), ([1,5,6], -721373184), ([1,5,7], -686577600), ([1,5,8], -685045440), ([1,5,9], -566343360), ([1,5,10], -524733120), ([1,5,11], -371436480), ([1,5,13], -546885720), ([1,5,15], -1029388680), ([1,5,16], -1758518760), ([1,5,17], -1772907720), ([1,6,7], -186034464), ([1,6,8], -1329197760), ([1,6,9], -1138242240), ([1,6,10], -997606080), ([1,6,11], -745283520), ([1,6,13], -765863640), ([1,6,15], -1136680200), ([1,6,16], -2327164200), ([1,6,17], -1797301320), ([1,7,8], -823839744), ([1,7,9], -1594800000), ([1,7,10], -1329978240), ([1,7,11], -953470080), ([1,7,13], -814533840), ([1,7,15], -1114688880), ([1,7,16], -2299460400), ([1,7,17], -1763885040), ([1,8,8], -102466560), ([1,8,9], -697267200), ([1,8,10], -1705238016), ([1,8,11], -1265195520), ([1,8,12], -102466560), ([1,8,13], -880358400), ([1,8,14], -102466560), ([1,8,15], -987402240), ([1,8,16], -2041981440), ([1,8,17], -1427447040), ([1,9,9], -84403200), ([1,9,10], -590284800), ([1,9,11], -1145088000), ([1,9,12], -192974880), ([1,9,13], -820176480), ([1,9,14], -84403200), ([1,9,15], -649654560), ([1,9,16], -1586389920), ([1,9,17], -844980000), ([1,10,10], -116659200), ([1,10,11], -116659200), ([1,10,12], -361532640), ([1,10,13], -778050720), ([1,10,14], -116659200), ([1,10,15], -175142880), ([1,10,16], -874047840), ([1,10,17], -56313600), ([1,11,12], -241274880), ([1,11,13], -559319040), ([1,11,17], -56313600), ([1,12,17], -49274400), ([1,13,17], -35196000), ([1,14,17], -7039200), ([1,15,17], 7039200), ([1,16,17], 35196000), ([1,17,17], 63352800), ([2,2,8], -51233280), ([2,2,9], -42201600), ([2,2,10], -58329600), ([2,2,16], -1499904000), ([2,3,8], -102466560), ([2,3,9], -84403200), ([2,3,10], -116659200), ([2,3,11], -161280000), ([2,3,13], -388362240), ([2,3,15], -615444480), ([2,3,16], -4005550080), ([2,3,17], -842526720), ([2,4,5], -1442746368), ([2,4,6], -609029760), ([2,4,7], -113809920), ([2,4,8], -102466560), ([2,4,9], -84403200), ([2,4,10], -116659200), ([2,4,11], -74457600), ([2,4,13], -571824960), ([2,4,15], -1534303680), ([2,4,16], -4133483200), ([2,4,17], -2806856640), ([2,5,6], -1442746368), ([2,5,7], -1373155200), ([2,5,8], -1267624320), ([2,5,9], -1048283520), ([2,5,10], -932807040), ([2,5,11], -742872960), ([2,5,13], -1093771440), ([2,5,15], -2058777360), ([2,5,16], -5016941520), ([2,5,17], -3433188240), ([2,6,7], -372068928), ([2,6,8], -2555928960), ([2,6,9], -2192081280), ([2,6,10], -1878552960), ([2,6,11], -1490567040), ([2,6,13], -1531727280), ([2,6,15], -2273360400), ([2,6,16], -6154232400), ([2,6,17], -3481975440), ([2,7,8], -1545212928), ([2,7,9], -3105196800), ([2,7,10], -2543297280), ([2,7,11], -1906940160), ([2,7,13], -1629067680), ([2,7,15], -2229377760), ([2,7,16], -6098824800), ([2,7,17], -3415142880), ([2,8,8], -102466560), ([2,8,9], -1207664640), ([2,8,10], -3191350272), ([2,8,11], -2427924480), ([2,8,12], -102466560), ([2,8,13], -1658250240), ([2,8,14], -102466560), ([2,8,15], -1872337920), ([2,8,16], -5583866880), ([2,8,17], -2742266880), ([2,9,9], -84403200), ([2,9,10], -979507200), ([2,9,11], -2205772800), ([2,9,12], -301546560), ([2,9,13], -1555949760), ([2,9,14], -84403200), ([2,9,15], -1214905920), ([2,9,16], -4672683840), ([2,9,17], -1577332800), ([2,10,10], -116659200), ([2,10,11], -116659200), ([2,10,12], -606406080), ([2,10,13], -1439442240), ([2,10,14], -116659200), ([2,10,15], -233626560), ([2,10,16], -3247999680), ([2,11,12], -482549760), ([2,11,13], -1118638080), ([2,11,16], -1499904000), ([2,12,16], -749952000), ([2,14,16], 749952000), ([2,15,16], 1124928000), ([2,16,16], 1499904000), ([2,16,17], 1687392000), ([3,3,8], -51233280), ([3,3,9], -42201600), ([3,3,10], -58329600), ([3,3,11], -161280000), ([3,3,13], -388362240), ([3,3,15], -615444480), ([3,3,16], -2505646080), ([3,3,17], -842526720), ([3,4,5], -1442746368), ([3,4,6], -609029760), ([3,4,7], -113809920), ([3,4,8], -102466560), ([3,4,9], -84403200), ([3,4,10], -116659200), ([3,4,11], -235737600), ([3,4,13], -960187200), ([3,4,15], -2149748160), ([3,4,16], -5139225280), ([3,4,17], -3649383360), ([3,5,6], -1442746368), ([3,5,7], -1373155200), ([3,5,8], -1267624320), ([3,5,9], -1048283520), ([3,5,10], -932807040), ([3,5,11], -904152960), ([3,5,13], -1482133680), ([3,5,15], -2674221840), ([3,5,16], -6022683600), ([3,5,17], -4275714960), ([3,6,7], -372068928), ([3,6,8], -2555928960), ([3,6,9], -2192081280), ([3,6,10], -1878552960), ([3,6,11], -1651847040), ([3,6,13], -1920089520), ([3,6,15], -2888804880), ([3,6,16], -7159974480), ([3,6,17], -4324502160), ([3,7,8], -1545212928), ([3,7,9], -3105196800), ([3,7,10], -2543297280), ([3,7,11], -2068220160), ([3,7,13], -2017429920), ([3,7,15], -2844822240), ([3,7,16], -7104566880), ([3,7,17], -4257669600), ([3,8,8], -102466560), ([3,8,9], -1207664640), ([3,8,10], -3191350272), ([3,8,11], -2589204480), ([3,8,12], -102466560), ([3,8,13], -2046612480), ([3,8,14], -102466560), ([3,8,15], -2487782400), ([3,8,16], -6589608960), ([3,8,17], -3584793600), ([3,9,9], -84403200), ([3,9,10], -979507200), ([3,9,11], -2367052800), ([3,9,12], -301546560), ([3,9,13], -1944312000), ([3,9,14], -84403200), ([3,9,15], -1830350400), ([3,9,16], -5678425920), ([3,9,17], -2419859520), ([3,10,10], -116659200), ([3,10,11], -277939200), ([3,10,12], -606406080), ([3,10,13], -1827804480), ([3,10,14], -116659200), ([3,10,15], -849071040), ([3,10,16], -4253741760), ([3,10,17], -842526720), ([3,11,11], -161280000), ([3,11,12], -563189760), ([3,11,13], -1507000320), ([3,11,14], 80640000), ([3,11,15], -494484480), ([3,11,16], -2344366080), ([3,11,17], -661086720), ([3,12,13], -194181120), ([3,12,15], -307722240), ([3,12,16], -1252823040), ([3,12,17], -421263360), ([3,13,14], 194181120), ([3,13,15], 291271680), ([3,13,16], 388362240), ([3,13,17], 436907520), ([3,14,15], 307722240), ([3,14,16], 1252823040), ([3,14,17], 421263360), ([3,15,15], 461583360), ([3,15,16], 2494679040), ([3,15,17], 1324270080), ([3,16,16], 2505646080), ([3,16,17], 3661378560), ([3,17,17], 947842560), ([4,4,5], -1442746368), ([4,4,6], -609029760), ([4,4,7], -113809920), ([4,4,8], -51233280), ([4,4,9], -42201600), ([4,4,10], -58329600), ([4,4,11], -74457600), ([4,4,13], -571824960), ([4,4,15], -1534303680), ([4,4,16], -2633579200), ([4,4,17], -2806856640), ([4,5,5], -1442746368), ([4,5,6], -3494522496), ([4,5,7], -2929711488), ([4,5,8], -2710370688), ([4,5,9], -2491029888), ([4,5,10], -2375553408), ([4,5,11], -2260076928), ([4,5,12], -721373184), ([4,5,13], -1665596400), ([4,5,14], 721373184), ([4,5,15], -2511021264), ([4,5,16], -4707870352), ([4,5,17], -4616955216), ([4,6,6], -609029760), ([4,6,7], -1094908608), ([4,6,8], -3164958720), ([4,6,9], -2801111040), ([4,6,10], -2487582720), ([4,6,11], -2174054400), ([4,6,12], -304514880), ([4,6,13], -2103552240), ([4,6,14], 304514880), ([4,6,15], -3350891760), ([4,6,16], -6678877840), ([4,6,17], -5603673600), ([4,7,7], -113809920), ([4,7,8], -1659022848), ([4,7,9], -3219006720), ([4,7,10], -2657107200), ([4,7,11], -2095207680), ([4,7,12], -56904960), ([4,7,13], -2200892640), ([4,7,14], 56904960), ([4,7,15], -3678324000), ([4,7,16], -7118690080), ([4,7,17], -6093963360), ([4,8,8], -102466560), ([4,8,9], -1207664640), ([4,8,10], -3191350272), ([4,8,11], -2502382080), ([4,8,12], -102466560), ([4,8,13], -2230075200), ([4,8,14], -102466560), ([4,8,15], -3406641600), ([4,8,16], -6717542080), ([4,8,17], -5549123520), ([4,9,9], -84403200), ([4,9,10], -979507200), ([4,9,11], -2280230400), ([4,9,12], -301546560), ([4,9,13], -2127774720), ([4,9,14], -84403200), ([4,9,15], -2749209600), ([4,9,16], -5806359040), ([4,9,17], -4384189440), ([4,10,10], -116659200), ([4,10,11], -191116800), ([4,10,12], -606406080), ([4,10,13], -2011267200), ([4,10,14], -116659200), ([4,10,15], -1767930240), ([4,10,16], -4381674880), ([4,10,17], -2806856640), ([4,11,11], -74457600), ([4,11,12], -519778560), ([4,11,13], -1690463040), ([4,11,14], 37228800), ([4,11,15], -1478460480), ([4,11,16], -2559121600), ([4,11,17], -2723091840), ([4,12,13], -285912480), ([4,12,15], -767151840), ([4,12,16], -1316789600), ([4,12,17], -1403428320), ([4,13,14], 285912480), ([4,13,15], 428868720), ([4,13,16], 571824960), ([4,13,17], 643303080), ([4,14,15], 767151840), ([4,14,16], 1316789600), ([4,14,17], 1403428320), ([4,15,15], 1150727760), ([4,15,16], 3509488080), ([4,15,17], 3831234120), ([4,16,16], 2633579200), ([4,16,17], 5769633240), ([4,17,17], 3157713720), ([5,5,6], -1442746368), ([5,5,7], -1373155200), ([5,5,8], -1216391040), ([5,5,9], -1006081920), ([5,5,10], -874477440), ([5,5,11], -742872960), ([5,5,13], -1093771440), ([5,5,15], -2058777360), ([5,5,16], -3517037520), ([5,5,17], -3433188240), ([5,6,6], -1442746368), ([5,6,7], -3187970496), ([5,6,8], -5163833088), ([5,6,9], -4598707968), ([5,6,10], -4137447168), ([5,6,11], -3676186368), ([5,6,12], -721373184), ([5,6,13], -2625498720), ([5,6,14], 721373184), ([5,6,15], -3250077984), ([5,6,16], -6728619552), ([5,6,17], -5292074016), ([5,7,7], -1373155200), ([5,7,8], -4083525888), ([5,7,9], -5442232320), ([5,7,10], -4732600320), ([5,7,11], -4022968320), ([5,7,12], -686577600), ([5,7,13], -2722839120), ([5,7,14], 686577600), ([5,7,15], -3258288720), ([5,7,16], -6742803120), ([5,7,17], -5303531520), ([5,8,8], -1267624320), ([5,8,9], -3336702720), ([5,8,10], -5172655872), ([5,8,11], -4335955200), ([5,8,12], -685045440), ([5,8,13], -2752021680), ([5,8,14], 480112320), ([5,8,15], -3057246960), ([5,8,16], -6435842640), ([5,8,17], -4864652640), ([5,9,9], -1048283520), ([5,9,10], -2759535360), ([5,9,11], -3912526080), ([5,9,12], -783486720), ([5,9,13], -2649721200), ([5,9,14], 397536960), ([5,9,15], -2550773040), ([5,9,16], -5725937040), ([5,9,17], -3926155680), ([5,10,10], -932807040), ([5,10,11], -1675680000), ([5,10,12], -1014480000), ([5,10,13], -2533213680), ([5,10,14], 291414720), ([5,10,15], -1680293040), ([5,10,16], -4448985360), ([5,10,17], -2515021920), ([5,11,11], -742872960), ([5,11,12], -853986240), ([5,11,13], -2212409520), ([5,11,14], 371436480), ([5,11,15], -1501622640), ([5,11,16], -2774164560), ([5,11,17], -2597456160), ([5,12,13], -546885720), ([5,12,15], -1029388680), ([5,12,16], -1758518760), ([5,12,17], -1716594120), ([5,13,14], 546885720), ([5,13,15], 820328580), ([5,13,16], 1093771440), ([5,13,17], 1230492870), ([5,14,15], 1029388680), ([5,14,16], 1758518760), ([5,14,17], 1716594120), ([5,15,15], 1544083020), ([5,15,16], 4696555500), ([5,15,17], 4891015710), ([5,16,16], 3517037520), ([5,16,17], 7389855450), ([5,17,17], 3862336770), ([6,6,7], -372068928), ([6,6,8], -2504695680), ([6,6,9], -2149879680), ([6,6,10], -1820223360), ([6,6,11], -1490567040), ([6,6,13], -1531727280), ([6,6,15], -2273360400), ([6,6,16], -4654328400), ([6,6,17], -3481975440), ([6,7,7], -372068928), ([6,7,8], -4370744256), ([6,7,9], -5584943808), ([6,7,10], -4677259968), ([6,7,11], -3769576128), ([6,7,12], -186034464), ([6,7,13], -3160794960), ([6,7,14], 186034464), ([6,7,15], -4223686464), ([6,7,16], -8881180272), ([6,7,17], -6478540776), ([6,8,8], -2555928960), ([6,8,9], -5768805120), ([6,8,10], -7406706432), ([6,8,11], -6371953920), ([6,8,12], -1329197760), ([6,8,13], -3189977520), ([6,8,14], 1124264640), ([6,8,15], -2305601520), ([6,8,16], -6284828880), ([6,8,17], -3464097120), ([6,9,9], -2192081280), ([6,9,10], -4849079040), ([6,9,11], -5804017920), ([6,9,12], -1355385600), ([6,9,13], -3087677040), ([6,9,14], 969435840), ([6,9,15], -1907507760), ([6,9,16], -5719430160), ([6,9,17], -2688170400), ([6,10,10], -1878552960), ([6,10,11], -3369120000), ([6,10,12], -1487352960), ([6,10,13], -2971169520), ([6,10,14], 764287680), ([6,10,15], -1185566640), ([6,10,16], -4640530320), ([6,10,17], -1499844960), ([6,11,11], -1490567040), ([6,11,12], -1227833280), ([6,11,13], -2650365360), ([6,11,14], 745283520), ([6,11,15], -1155435120), ([6,11,16], -3163761360), ([6,11,17], -1805087520), ([6,12,13], -765863640), ([6,12,15], -1136680200), ([6,12,16], -2327164200), ([6,12,17], -1740987720), ([6,13,14], 765863640), ([6,13,15], 1148795460), ([6,13,16], 1531727280), ([6,13,17], 1723193190), ([6,14,15], 1136680200), ([6,14,16], 2327164200), ([6,14,17], 1740987720), ([6,15,15], 1705020300), ([6,15,16], 5764106700), ([6,15,17], 5169012030), ([6,16,16], 4654328400), ([6,16,17], 8718094890), ([6,17,17], 3917222370), ([7,7,8], -1493979648), ([7,7,9], -3062995200), ([7,7,10], -2484967680), ([7,7,11], -1906940160), ([7,7,13], -1629067680), ([7,7,15], -2229377760), ([7,7,16], -4598920800), ([7,7,17], -3415142880), ([7,8,8], -1545212928), ([7,8,9], -5671204608), ([7,8,10], -7060734720), ([7,8,11], -5777611008), ([7,8,12], -823839744), ([7,8,13], -3287317920), ([7,8,14], 618906624), ([7,8,15], -3019655904), ([7,8,16], -7240137312), ([7,8,17], -4534320096), ([7,9,9], -3105196800), ([7,9,10], -6426938880), ([7,9,11], -7133506560), ([7,9,12], -1811943360), ([7,9,13], -3185017440), ([7,9,14], 1425993600), ([7,9,15], -1178688480), ([7,9,16], -4750907040), ([7,9,17], -1594082880), ([7,10,10], -2543297280), ([7,10,11], -4450237440), ([7,10,12], -1819725120), ([7,10,13], -3068509920), ([7,10,14], 1096659840), ([7,10,15], -643025760), ([7,10,16], -3920378400), ([7,10,17], -685175040), ([7,11,11], -1906940160), ([7,11,12], -1436019840), ([7,11,13], -2747705760), ([7,11,14], 953470080), ([7,11,15], -799172640), ([7,11,16], -2691980640), ([7,11,17], -1269835200), ([7,12,13], -814533840), ([7,12,15], -1114688880), ([7,12,16], -2299460400), ([7,12,17], -1707571440), ([7,13,14], 814533840), ([7,13,15], 1221800760), ([7,13,16], 1629067680), ([7,13,17], 1832701140), ([7,14,15], 1114688880), ([7,14,16], 2299460400), ([7,14,17], 1707571440), ([7,15,15], 1672033320), ([7,15,16], 5678568360), ([7,15,17], 5069407140), ([7,16,16], 4598920800), ([7,16,17], 8588928780), ([7,17,17], 3842035740), ([8,8,8], -51233280), ([8,8,9], -1165463040), ([8,8,10], -3133020672), ([8,8,11], -2427924480), ([8,8,12], -102466560), ([8,8,13], -1658250240), ([8,8,14], -102466560), ([8,8,15], -1872337920), ([8,8,16], -4083962880), ([8,8,17], -2742266880), ([8,9,9], -1156431360), ([8,9,10], -5074993152), ([8,9,11], -5654492160), ([8,9,12], -914410560), ([8,9,13], -3214200000), ([8,9,14], 323527680), ([8,9,15], -2321647680), ([8,9,16], -6235947840), ([8,9,17], -3171205440), ([8,10,10], -3140116992), ([8,10,11], -5516808192), ([8,10,12], -2194984896), ([8,10,13], -3097692480), ([8,10,14], 1266986496), ([8,10,15], 123203904), ([8,10,16], -2859834048), ([8,10,17], 601485696), ([8,11,11], -2376691200), ([8,11,12], -1747745280), ([8,11,13], -2776888320), ([8,11,14], 1060262400), ([8,11,15], -128244480), ([8,11,16], -1758504960), ([8,11,17], -126126720), ([8,12,12], -51233280), ([8,12,13], -880358400), ([8,12,14], -102466560), ([8,12,15], -987402240), ([8,12,16], -2041981440), ([8,12,17], -1371133440), ([8,13,13], -51233280), ([8,13,14], 675425280), ([8,13,15], 1064371200), ([8,13,16], 1555783680), ([8,13,17], 1750256640), ([8,14,14], -51233280), ([8,14,15], 782469120), ([8,14,16], 2041981440), ([8,14,17], 1576066560), ([8,15,15], 1276170240), ([8,15,16], 4832843520), ([8,15,17], 4252738560), ([8,16,16], 4083962880), ([8,16,17], 7541658240), ([8,17,17], 3289983360), ([9,9,9], -42201600), ([9,9,10], -921177600), ([9,9,11], -2205772800), ([9,9,12], -301546560), ([9,9,13], -1555949760), ([9,9,14], -84403200), ([9,9,15], -1214905920), ([9,9,16], -3172779840), ([9,9,17], -1577332800), ([9,10,10], -937305600), ([9,10,11], -3100876800), ([9,10,12], -1297175040), ([9,10,13], -2995392000), ([9,10,14], 188160000), ([9,10,15], -864698880), ([9,10,16], -4142430720), ([9,10,17], -701582400), ([9,11,11], -2163571200), ([9,11,12], -1844781120), ([9,11,13], -2674587840), ([9,11,14], 976281600), ([9,11,15], 376121280), ([9,11,16], -1051410240), ([9,11,17], 809208000), ([9,12,12], -150773280), ([9,12,13], -820176480), ([9,12,14], 24168480), ([9,12,15], -486797040), ([9,12,16], -1369246560), ([9,12,17], -544380120), ([9,13,13], -42201600), ([9,13,14], 651370080), ([9,13,15], 1019256720), ([9,13,16], 1471546560), ([9,13,17], 1655489880), ([9,14,14], -42201600), ([9,14,15], 480848160), ([9,14,16], 1586389920), ([9,14,17], 957472800), ([9,15,15], 805675440), ([9,15,16], 3510087600), ([9,15,17], 2623621560), ([9,16,16], 3172779840), ([9,16,17], 5315516520), ([9,17,17], 1943305800), ([10,10,10], -58329600), ([10,10,11], -116659200), ([10,10,12], -606406080), ([10,10,13], -1439442240), ([10,10,14], -116659200), ([10,10,15], -233626560), ([10,10,16], -1748095680), ([10,11,11], -58329600), ([10,11,12], -1088955840), ([10,11,13], -2558080320), ([10,11,14], -116659200), ([10,11,15], -233626560), ([10,11,16], -1748095680), ([10,12,12], -303203040), ([10,12,13], -778050720), ([10,12,14], 128214240), ([10,12,15], 192167280), ([10,12,16], -384300960), ([10,12,17], 550965240), ([10,13,13], -58329600), ([10,13,14], 544732320), ([10,13,15], 875428080), ([10,13,16], 1322783040), ([10,13,17], 1488130920), ([10,14,14], -58329600), ([10,14,15], -58175520), ([10,14,16], 874047840), ([10,14,17], 233318400), ([10,15,15], 29395920), ([10,15,16], 1428039120), ([10,15,17], 364906680), ([10,16,16], 1748095680), ([10,16,17], 2199926040), ([10,17,17], 233318400), ([11,11,12], -482549760), ([11,11,13], -1118638080), ([11,12,12], -241274880), ([11,12,13], -559319040), ([11,12,14], 241274880), ([11,12,15], 361912320), ([11,12,16], 482549760), ([11,12,17], 542868480), ([11,13,14], 559319040), ([11,13,15], 838978560), ([11,13,16], 1118638080), ([11,13,17], 1258467840)]
theorem block001_data : block001 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (120637440 : Int) atom0015) (SparsePolynomial.scale (51233280 : Int) atom0016)) (SparsePolynomial.merge (SparsePolynomial.scale (42201600 : Int) atom0017) (SparsePolynomial.merge (SparsePolynomial.scale (58329600 : Int) atom0018) (SparsePolynomial.scale (175472640 : Int) atom0019)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (93744000 : Int) atom0020) (SparsePolynomial.scale (10080000 : Int) atom0021)) (SparsePolynomial.merge (SparsePolynomial.scale (24272640 : Int) atom0022) (SparsePolynomial.merge (SparsePolynomial.scale (38465280 : Int) atom0023) (SparsePolynomial.scale (156602880 : Int) atom0024))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52657920 : Int) atom0025) (SparsePolynomial.scale (90171648 : Int) atom0026)) (SparsePolynomial.merge (SparsePolynomial.scale (38064360 : Int) atom0027) (SparsePolynomial.merge (SparsePolynomial.scale (7113120 : Int) atom0028) (SparsePolynomial.scale (4653600 : Int) atom0029)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (35739060 : Int) atom0030) (SparsePolynomial.scale (95893980 : Int) atom0031)) (SparsePolynomial.merge (SparsePolynomial.scale (164598700 : Int) atom0032) (SparsePolynomial.merge (SparsePolynomial.scale (175428540 : Int) atom0033) (SparsePolynomial.scale (90171648 : Int) atom0034)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (85822200 : Int) atom0035) (SparsePolynomial.scale (72822360 : Int) atom0036)) (SparsePolynomial.merge (SparsePolynomial.scale (60242520 : Int) atom0037) (SparsePolynomial.merge (SparsePolynomial.scale (51009240 : Int) atom0038) (SparsePolynomial.scale (46429560 : Int) atom0039)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (68360715 : Int) atom0040) (SparsePolynomial.scale (128673585 : Int) atom0041)) (SparsePolynomial.merge (SparsePolynomial.scale (219814845 : Int) atom0042) (SparsePolynomial.merge (SparsePolynomial.scale (214574265 : Int) atom0043) (SparsePolynomial.scale (23254308 : Int) atom0044))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (153341400 : Int) atom0045) (SparsePolynomial.scale (131729880 : Int) atom0046)) (SparsePolynomial.merge (SparsePolynomial.scale (110118360 : Int) atom0047) (SparsePolynomial.merge (SparsePolynomial.scale (93160440 : Int) atom0048) (SparsePolynomial.scale (95732955 : Int) atom0049)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (142085025 : Int) atom0050) (SparsePolynomial.scale (290895525 : Int) atom0051)) (SparsePolynomial.merge (SparsePolynomial.scale (217623465 : Int) atom0052) (SparsePolynomial.merge (SparsePolynomial.scale (90171648 : Int) atom0053) (SparsePolynomial.scale (188799600 : Int) atom0054))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (151664880 : Int) atom0055) (SparsePolynomial.scale (119183760 : Int) atom0056)) (SparsePolynomial.merge (SparsePolynomial.scale (101816730 : Int) atom0057) (SparsePolynomial.merge (SparsePolynomial.scale (139336110 : Int) atom0058) (SparsePolynomial.scale (287432550 : Int) atom0059)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (213446430 : Int) atom0060) (SparsePolynomial.scale (63799680 : Int) atom0061)) (SparsePolynomial.merge (SparsePolynomial.scale (185764032 : Int) atom0062) (SparsePolynomial.merge (SparsePolynomial.scale (145341120 : Int) atom0063) (SparsePolynomial.scale (97236480 : Int) atom0064))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (110616960 : Int) atom0065) (SparsePolynomial.scale (255247680 : Int) atom0066)) (SparsePolynomial.merge (SparsePolynomial.scale (171391680 : Int) atom0067) (SparsePolynomial.merge (SparsePolynomial.scale (48652800 : Int) atom0068) (SparsePolynomial.scale (132585600 : Int) atom0069)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13571460 : Int) atom0070) (SparsePolynomial.scale (91971660 : Int) atom0071)) (SparsePolynomial.merge (SparsePolynomial.scale (70656420 : Int) atom0072) (SparsePolynomial.merge (SparsePolynomial.scale (198298740 : Int) atom0073) (SparsePolynomial.scale (98583300 : Int) atom0074)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30609180 : Int) atom0075) (SparsePolynomial.scale (82673940 : Int) atom0076)) (SparsePolynomial.merge (SparsePolynomial.scale (7310460 : Int) atom0077) (SparsePolynomial.merge (SparsePolynomial.scale (109255980 : Int) atom0078) (SparsePolynomial.scale (30159360 : Int) atom0079)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (69914880 : Int) atom0080) (SparsePolynomial.scale (28062720 : Int) atom0081)) (SparsePolynomial.merge (SparsePolynomial.scale (41045760 : Int) atom0082) (SparsePolynomial.merge (SparsePolynomial.scale (54028800 : Int) atom0083) (SparsePolynomial.scale (67011840 : Int) atom0084))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (79994880 : Int) atom0085) (SparsePolynomial.scale (92977920 : Int) atom0086)) (SparsePolynomial.merge (SparsePolynomial.scale (105960960 : Int) atom0087) (SparsePolynomial.merge (SparsePolynomial.scale (112539840 : Int) atom0088) (SparsePolynomial.scale (126651840 : Int) atom0089)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (137618880 : Int) atom0090) (SparsePolynomial.scale (157893120 : Int) atom0091)) (SparsePolynomial.merge (SparsePolynomial.scale (30885120 : Int) atom0092) (SparsePolynomial.merge (SparsePolynomial.scale (58044000 : Int) atom0093) (SparsePolynomial.scale (3519600 : Int) atom0094)))))))) := by decide +kernel
theorem block001_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block001 := by
  rw [block001_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0015_nonneg g hg hA hB) (atom0016_nonneg g hg hA hB)) (add_nonneg (atom0017_nonneg g hg hA hB) (add_nonneg (atom0018_nonneg g hg hA hB) (atom0019_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0020_nonneg g hg hA hB) (atom0021_nonneg g hg hA hB)) (add_nonneg (atom0022_nonneg g hg hA hB) (add_nonneg (atom0023_nonneg g hg hA hB) (atom0024_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0025_nonneg g hg hA hB) (atom0026_nonneg g hg hA hB)) (add_nonneg (atom0027_nonneg g hg hA hB) (add_nonneg (atom0028_nonneg g hg hA hB) (atom0029_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0030_nonneg g hg hA hB) (atom0031_nonneg g hg hA hB)) (add_nonneg (atom0032_nonneg g hg hA hB) (add_nonneg (atom0033_nonneg g hg hA hB) (atom0034_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0035_nonneg g hg hA hB) (atom0036_nonneg g hg hA hB)) (add_nonneg (atom0037_nonneg g hg hA hB) (add_nonneg (atom0038_nonneg g hg hA hB) (atom0039_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0040_nonneg g hg hA hB) (atom0041_nonneg g hg hA hB)) (add_nonneg (atom0042_nonneg g hg hA hB) (add_nonneg (atom0043_nonneg g hg hA hB) (atom0044_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0045_nonneg g hg hA hB) (atom0046_nonneg g hg hA hB)) (add_nonneg (atom0047_nonneg g hg hA hB) (add_nonneg (atom0048_nonneg g hg hA hB) (atom0049_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0050_nonneg g hg hA hB) (atom0051_nonneg g hg hA hB)) (add_nonneg (atom0052_nonneg g hg hA hB) (add_nonneg (atom0053_nonneg g hg hA hB) (atom0054_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0055_nonneg g hg hA hB) (atom0056_nonneg g hg hA hB)) (add_nonneg (atom0057_nonneg g hg hA hB) (add_nonneg (atom0058_nonneg g hg hA hB) (atom0059_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0060_nonneg g hg hA hB) (atom0061_nonneg g hg hA hB)) (add_nonneg (atom0062_nonneg g hg hA hB) (add_nonneg (atom0063_nonneg g hg hA hB) (atom0064_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0065_nonneg g hg hA hB) (atom0066_nonneg g hg hA hB)) (add_nonneg (atom0067_nonneg g hg hA hB) (add_nonneg (atom0068_nonneg g hg hA hB) (atom0069_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0070_nonneg g hg hA hB) (atom0071_nonneg g hg hA hB)) (add_nonneg (atom0072_nonneg g hg hA hB) (add_nonneg (atom0073_nonneg g hg hA hB) (atom0074_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0075_nonneg g hg hA hB) (atom0076_nonneg g hg hA hB)) (add_nonneg (atom0077_nonneg g hg hA hB) (add_nonneg (atom0078_nonneg g hg hA hB) (atom0079_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0080_nonneg g hg hA hB) (atom0081_nonneg g hg hA hB)) (add_nonneg (atom0082_nonneg g hg hA hB) (add_nonneg (atom0083_nonneg g hg hA hB) (atom0084_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0085_nonneg g hg hA hB) (atom0086_nonneg g hg hA hB)) (add_nonneg (atom0087_nonneg g hg hA hB) (add_nonneg (atom0088_nonneg g hg hA hB) (atom0089_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0090_nonneg g hg hA hB) (atom0091_nonneg g hg hA hB)) (add_nonneg (atom0092_nonneg g hg hA hB) (add_nonneg (atom0093_nonneg g hg hA hB) (atom0094_nonneg g hg hA hB))))))))

end APPT.Finite18
