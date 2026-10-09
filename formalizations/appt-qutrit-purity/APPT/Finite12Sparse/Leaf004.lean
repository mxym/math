import APPT.Finite12Sparse.Base00
import APPT.Finite12Sparse.Base01
import APPT.Finite12Sparse.Base02
import APPT.Finite12Sparse.Base03
import APPT.Finite12Sparse.Base04
import APPT.Finite12Sparse.Base05
import APPT.Finite12Sparse.Base06
import APPT.Finite12Sparse.Base07
import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def atom0320 : SparsePolynomial.Poly := [([8,9,11], 1)]
theorem eval_atom0320 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0320 = ((g 8) * (g 9) * (g 11)) := by
  norm_num [atom0320, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0320_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (225024 : Int) atom0320) := by
  rw [SparsePolynomial.eval_scale, eval_atom0320]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0321 : SparsePolynomial.Poly := [([8,10,10], 1)]
theorem eval_atom0321 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0321 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom0321, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0321_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (171072 : Int) atom0321) := by
  rw [SparsePolynomial.eval_scale, eval_atom0321]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0322 : SparsePolynomial.Poly := [([8,10,11], 1)]
theorem eval_atom0322 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0322 = ((g 8) * (g 10) * (g 11)) := by
  norm_num [atom0322, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0322_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (290688 : Int) atom0322) := by
  rw [SparsePolynomial.eval_scale, eval_atom0322]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0323 : SparsePolynomial.Poly := [([8,11,11], 1)]
theorem eval_atom0323 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0323 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom0323, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0323_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90240 : Int) atom0323) := by
  rw [SparsePolynomial.eval_scale, eval_atom0323]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0324 : SparsePolynomial.Poly := [([9,9,9], 1)]
theorem eval_atom0324 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0324 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom0324, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0324_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47616 : Int) atom0324) := by
  rw [SparsePolynomial.eval_scale, eval_atom0324]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0325 : SparsePolynomial.Poly := [([9,9,10], 1)]
theorem eval_atom0325 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0325 = ((g 9) * (g 9) * (g 10)) := by
  norm_num [atom0325, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0325_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (163776 : Int) atom0325) := by
  rw [SparsePolynomial.eval_scale, eval_atom0325]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0326 : SparsePolynomial.Poly := [([9,9,11], 1)]
theorem eval_atom0326 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0326 = ((g 9) * (g 9) * (g 11)) := by
  norm_num [atom0326, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0326_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (108672 : Int) atom0326) := by
  rw [SparsePolynomial.eval_scale, eval_atom0326]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0327 : SparsePolynomial.Poly := [([9,10,10], 1)]
theorem eval_atom0327 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0327 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom0327, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0327_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (190080 : Int) atom0327) := by
  rw [SparsePolynomial.eval_scale, eval_atom0327]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0328 : SparsePolynomial.Poly := [([9,10,11], 1)]
theorem eval_atom0328 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0328 = ((g 9) * (g 10) * (g 11)) := by
  norm_num [atom0328, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0328_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (298752 : Int) atom0328) := by
  rw [SparsePolynomial.eval_scale, eval_atom0328]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0329 : SparsePolynomial.Poly := [([9,11,11], 1)]
theorem eval_atom0329 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0329 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom0329, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0329_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (76032 : Int) atom0329) := by
  rw [SparsePolynomial.eval_scale, eval_atom0329]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0330 : SparsePolynomial.Poly := [([10,10,10], 1)]
theorem eval_atom0330 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0330 = ((g 10) * (g 10) * (g 10)) := by
  norm_num [atom0330, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0330_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (69696 : Int) atom0330) := by
  rw [SparsePolynomial.eval_scale, eval_atom0330]
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 10) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0331 : SparsePolynomial.Poly := [([10,10,11], 1)]
theorem eval_atom0331 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0331 = ((g 10) * (g 10) * (g 11)) := by
  norm_num [atom0331, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0331_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (179520 : Int) atom0331) := by
  rw [SparsePolynomial.eval_scale, eval_atom0331]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0332 : SparsePolynomial.Poly := [([10,11,11], 1)]
theorem eval_atom0332 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0332 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom0332, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0332_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (114048 : Int) atom0332) := by
  rw [SparsePolynomial.eval_scale, eval_atom0332]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0333 : SparsePolynomial.Poly := [([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,0,9], -2), ([0,0,10], -2), ([0,0,11], -2), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -6), ([0,1,7], -4), ([0,1,8], -4), ([0,1,9], -4), ([0,1,10], -4), ([0,1,11], -4), ([0,2,2], -2), ([0,2,3], -4), ([0,2,4], -4), ([0,2,5], -4), ([0,2,6], -8), ([0,2,7], -6), ([0,2,8], -4), ([0,2,9], -4), ([0,2,10], -4), ([0,2,11], -4), ([0,3,3], -2), ([0,3,4], -4), ([0,3,5], -4), ([0,3,6], -8), ([0,3,7], -6), ([0,3,8], -4), ([0,3,9], -4), ([0,3,10], -4), ([0,3,11], -4), ([0,4,4], -2), ([0,4,5], -4), ([0,4,6], -8), ([0,4,7], -6), ([0,4,8], -4), ([0,4,9], -4), ([0,4,10], -4), ([0,4,11], -4), ([0,5,5], -2), ([0,5,6], -8), ([0,5,7], -6), ([0,5,8], -4), ([0,5,9], -4), ([0,5,10], -4), ([0,5,11], -4), ([0,6,6], -6), ([0,6,7], -10), ([0,6,8], -8), ([0,6,9], -8), ([0,6,10], -4), ([0,6,11], -4), ([0,7,7], -4), ([0,7,8], -8), ([0,7,9], -8), ([0,7,10], -4), ([0,7,11], -4), ([0,8,8], -4), ([0,8,9], -8), ([0,8,10], -4), ([0,8,11], -4), ([0,9,9], -4), ([0,9,10], -4), ([0,9,11], -4), ([1,1,2], -2), ([1,1,3], -2), ([1,1,4], -2), ([1,1,5], -2), ([1,1,6], -4), ([1,1,7], -2), ([1,1,8], -2), ([1,1,9], -4), ([1,1,10], -4), ([1,1,11], -4), ([1,2,2], -4), ([1,2,3], -8), ([1,2,4], -8), ([1,2,5], -8), ([1,2,6], -12), ([1,2,7], -8), ([1,2,8], -6), ([1,2,9], -10), ([1,2,10], -8), ([1,2,11], -8), ([1,3,3], -4), ([1,3,4], -8), ([1,3,5], -8), ([1,3,6], -12), ([1,3,7], -8), ([1,3,8], -6), ([1,3,9], -10), ([1,3,10], -8), ([1,3,11], -8), ([1,4,4], -4), ([1,4,5], -8), ([1,4,6], -12), ([1,4,7], -8), ([1,4,8], -6), ([1,4,9], -10), ([1,4,10], -8), ([1,4,11], -8), ([1,5,5], -4), ([1,5,6], -12), ([1,5,7], -8), ([1,5,8], -6), ([1,5,9], -10), ([1,5,10], -8), ([1,5,11], -8), ([1,6,6], -8), ([1,6,7], -12), ([1,6,8], -10), ([1,6,9], -14), ([1,6,10], -8), ([1,6,11], -8), ([1,7,7], -4), ([1,7,8], -8), ([1,7,9], -12), ([1,7,10], -8), ([1,7,11], -8), ([1,8,8], -4), ([1,8,9], -8), ([1,8,10], -4), ([1,8,11], -4), ([1,9,9], -4), ([1,9,10], -4), ([1,9,11], -4), ([2,2,2], -2), ([2,2,3], -6), ([2,2,4], -6), ([2,2,5], -6), ([2,2,6], -8), ([2,2,7], -6), ([2,2,8], -4), ([2,2,9], -6), ([2,2,10], -4), ([2,2,11], -6), ([2,3,3], -6), ([2,3,4], -12), ([2,3,5], -12), ([2,3,6], -16), ([2,3,7], -12), ([2,3,8], -8), ([2,3,9], -12), ([2,3,10], -8), ([2,3,11], -12), ([2,4,4], -6), ([2,4,5], -12), ([2,4,6], -16), ([2,4,7], -12), ([2,4,8], -8), ([2,4,9], -12), ([2,4,10], -8), ([2,4,11], -12), ([2,5,5], -6), ([2,5,6], -16), ([2,5,7], -12), ([2,5,8], -8), ([2,5,9], -12), ([2,5,10], -8), ([2,5,11], -12), ([2,6,6], -10), ([2,6,7], -16), ([2,6,8], -12), ([2,6,9], -16), ([2,6,10], -8), ([2,6,11], -12), ([2,7,7], -6), ([2,7,8], -10), ([2,7,9], -14), ([2,7,10], -8), ([2,7,11], -8), ([2,8,8], -4), ([2,8,9], -8), ([2,8,10], -4), ([2,8,11], -4), ([2,9,9], -4), ([2,9,10], -4), ([2,9,11], -4), ([3,3,3], -2), ([3,3,4], -6), ([3,3,5], -6), ([3,3,6], -8), ([3,3,7], -6), ([3,3,8], -4), ([3,3,9], -6), ([3,3,10], -4), ([3,3,11], -6), ([3,4,4], -6), ([3,4,5], -12), ([3,4,6], -16), ([3,4,7], -12), ([3,4,8], -8), ([3,4,9], -12), ([3,4,10], -8), ([3,4,11], -12), ([3,5,5], -6), ([3,5,6], -16), ([3,5,7], -12), ([3,5,8], -8), ([3,5,9], -12), ([3,5,10], -8), ([3,5,11], -12), ([3,6,6], -10), ([3,6,7], -16), ([3,6,8], -12), ([3,6,9], -16), ([3,6,10], -8), ([3,6,11], -12), ([3,7,7], -6), ([3,7,8], -10), ([3,7,9], -14), ([3,7,10], -8), ([3,7,11], -8), ([3,8,8], -4), ([3,8,9], -8), ([3,8,10], -4), ([3,8,11], -4), ([3,9,9], -4), ([3,9,10], -4), ([3,9,11], -4), ([4,4,4], -2), ([4,4,5], -6), ([4,4,6], -8), ([4,4,7], -6), ([4,4,8], -4), ([4,4,9], -6), ([4,4,10], -4), ([4,4,11], -6), ([4,5,5], -6), ([4,5,6], -16), ([4,5,7], -12), ([4,5,8], -8), ([4,5,9], -12), ([4,5,10], -8), ([4,5,11], -12), ([4,6,6], -10), ([4,6,7], -16), ([4,6,8], -12), ([4,6,9], -16), ([4,6,10], -8), ([4,6,11], -12), ([4,7,7], -6), ([4,7,8], -10), ([4,7,9], -14), ([4,7,10], -8), ([4,7,11], -8), ([4,8,8], -4), ([4,8,9], -8), ([4,8,10], -4), ([4,8,11], -4), ([4,9,9], -4), ([4,9,10], -4), ([4,9,11], -4), ([5,5,5], -2), ([5,5,6], -8), ([5,5,7], -6), ([5,5,8], -4), ([5,5,9], -6), ([5,5,10], -4), ([5,5,11], -6), ([5,6,6], -10), ([5,6,7], -16), ([5,6,8], -12), ([5,6,9], -16), ([5,6,10], -8), ([5,6,11], -12), ([5,7,7], -6), ([5,7,8], -10), ([5,7,9], -14), ([5,7,10], -8), ([5,7,11], -8), ([5,8,8], -4), ([5,8,9], -8), ([5,8,10], -4), ([5,8,11], -4), ([5,9,9], -4), ([5,9,10], -4), ([5,9,11], -4), ([6,6,6], -4), ([6,6,7], -10), ([6,6,8], -8), ([6,6,9], -10), ([6,6,10], -4), ([6,6,11], -6), ([6,7,7], -8), ([6,7,8], -14), ([6,7,9], -18), ([6,7,10], -8), ([6,7,11], -8), ([6,8,8], -6), ([6,8,9], -12), ([6,8,10], -4), ([6,8,11], -4), ([6,9,9], -6), ([6,9,10], -4), ([6,9,11], 4), ([6,10,11], 8), ([6,11,11], 8), ([7,7,7], -2), ([7,7,8], -6), ([7,7,9], -8), ([7,7,10], -4), ([7,7,11], -4), ([7,8,8], -6), ([7,8,9], -12), ([7,8,10], -4), ([7,8,11], -4), ([7,9,9], -6), ([7,9,10], -4), ([7,9,11], 4), ([7,10,11], 8), ([7,11,11], 8), ([8,8,8], -2), ([8,8,9], -6), ([8,8,10], -2), ([8,8,11], -2), ([8,9,9], -6), ([8,9,10], -4), ([8,9,11], 4), ([8,10,11], 8), ([8,11,11], 8), ([9,9,9], -2), ([9,9,10], -2), ([9,9,11], 6), ([9,10,11], 16), ([9,11,11], 16), ([10,10,11], 8), ([10,11,11], 16), ([11,11,11], 8)]
theorem atom0333_data : atom0333 = SparsePolynomial.monoTimes [] 1 base00 := by decide +kernel
theorem eval_atom0333 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0333 = (detA (outer g)) := by
  rw [atom0333_data, SparsePolynomial.eval_monoTimes, eval_base00]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0333_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6528 : Int) atom0333) := by
  rw [SparsePolynomial.eval_scale, eval_atom0333]
  have hb := base00_nonneg g hg hA hB
  rw [eval_base00] at hb
  have ht : 0 ≤ (detA (outer g)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0334 : SparsePolynomial.Poly := [([0,1,5], -4), ([1,1,5], -12), ([1,2,5], -16), ([1,3,5], -16), ([1,4,5], -16), ([1,5,5], -16), ([1,5,6], -8), ([1,5,7], -4), ([1,5,8], 4), ([1,5,9], 6), ([1,5,10], 10), ([1,5,11], 18)]
theorem atom0334_data : atom0334 = SparsePolynomial.monoTimes [1,5] 1 base01 := by decide +kernel
theorem eval_atom0334 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0334 = (quadA (outer g) ![2,1,2] * g 1 * g 5) := by
  rw [atom0334_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0334_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (128 : Int) atom0334) := by
  rw [SparsePolynomial.eval_scale, eval_atom0334]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0335 : SparsePolynomial.Poly := [([0,1,7], -4), ([1,1,7], -12), ([1,2,7], -16), ([1,3,7], -16), ([1,4,7], -16), ([1,5,7], -16), ([1,6,7], -8), ([1,7,7], -4), ([1,7,8], 4), ([1,7,9], 6), ([1,7,10], 10), ([1,7,11], 18)]
theorem atom0335_data : atom0335 = SparsePolynomial.monoTimes [1,7] 1 base01 := by decide +kernel
theorem eval_atom0335 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0335 = (quadA (outer g) ![2,1,2] * g 1 * g 7) := by
  rw [atom0335_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0335_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1360 : Int) atom0335) := by
  rw [SparsePolynomial.eval_scale, eval_atom0335]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0336 : SparsePolynomial.Poly := [([0,1,9], -4), ([1,1,9], -12), ([1,2,9], -16), ([1,3,9], -16), ([1,4,9], -16), ([1,5,9], -16), ([1,6,9], -8), ([1,7,9], -4), ([1,8,9], 4), ([1,9,9], 6), ([1,9,10], 10), ([1,9,11], 18)]
theorem atom0336_data : atom0336 = SparsePolynomial.monoTimes [1,9] 1 base01 := by decide +kernel
theorem eval_atom0336 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0336 = (quadA (outer g) ![2,1,2] * g 1 * g 9) := by
  rw [atom0336_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0336_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48 : Int) atom0336) := by
  rw [SparsePolynomial.eval_scale, eval_atom0336]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0337 : SparsePolynomial.Poly := [([0,1,10], -4), ([1,1,10], -12), ([1,2,10], -16), ([1,3,10], -16), ([1,4,10], -16), ([1,5,10], -16), ([1,6,10], -8), ([1,7,10], -4), ([1,8,10], 4), ([1,9,10], 6), ([1,10,10], 10), ([1,10,11], 18)]
theorem atom0337_data : atom0337 = SparsePolynomial.monoTimes [1,10] 1 base01 := by decide +kernel
theorem eval_atom0337 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0337 = (quadA (outer g) ![2,1,2] * g 1 * g 10) := by
  rw [atom0337_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0337_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1184 : Int) atom0337) := by
  rw [SparsePolynomial.eval_scale, eval_atom0337]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0338 : SparsePolynomial.Poly := [([0,1,11], -4), ([1,1,11], -12), ([1,2,11], -16), ([1,3,11], -16), ([1,4,11], -16), ([1,5,11], -16), ([1,6,11], -8), ([1,7,11], -4), ([1,8,11], 4), ([1,9,11], 6), ([1,10,11], 10), ([1,11,11], 18)]
theorem atom0338_data : atom0338 = SparsePolynomial.monoTimes [1,11] 1 base01 := by decide +kernel
theorem eval_atom0338 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0338 = (quadA (outer g) ![2,1,2] * g 1 * g 11) := by
  rw [atom0338_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0338_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1724 : Int) atom0338) := by
  rw [SparsePolynomial.eval_scale, eval_atom0338]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 1 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0339 : SparsePolynomial.Poly := [([0,3,3], -4), ([1,3,3], -12), ([2,3,3], -16), ([3,3,3], -16), ([3,3,4], -16), ([3,3,5], -16), ([3,3,6], -8), ([3,3,7], -4), ([3,3,8], 4), ([3,3,9], 6), ([3,3,10], 10), ([3,3,11], 18)]
theorem atom0339_data : atom0339 = SparsePolynomial.monoTimes [3,3] 1 base01 := by decide +kernel
theorem eval_atom0339 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0339 = (quadA (outer g) ![2,1,2] * g 3 * g 3) := by
  rw [atom0339_data, SparsePolynomial.eval_monoTimes, eval_base01]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0339_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (696 : Int) atom0339) := by
  rw [SparsePolynomial.eval_scale, eval_atom0339]
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base01_nonneg g hg hA hB
  rw [eval_base01] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,1,2] * g 3 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0340 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -16), ([1,1,4], -16), ([1,1,5], -16), ([1,1,6], -14), ([1,1,7], -10), ([1,1,8], -6), ([1,1,9], 2), ([1,1,10], 10), ([1,1,11], 18)]
theorem atom0340_data : atom0340 = SparsePolynomial.monoTimes [1,1] 1 base02 := by decide +kernel
theorem eval_atom0340 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0340 = (quadA (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0340_data, SparsePolynomial.eval_monoTimes, eval_base02]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0340_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1248 : Int) atom0340) := by
  rw [SparsePolynomial.eval_scale, eval_atom0340]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base02_nonneg g hg hA hB
  rw [eval_base02] at hb
  have ht : 0 ≤ (quadA (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0341 : SparsePolynomial.Poly := [([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,0,9], -2), ([0,0,10], -2), ([0,0,11], -2), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -6), ([0,1,7], -4), ([0,1,8], -4), ([0,1,9], -4), ([0,1,10], -4), ([0,1,11], -4), ([0,2,2], -2), ([0,2,3], -4), ([0,2,4], -4), ([0,2,5], -4), ([0,2,6], -8), ([0,2,7], -6), ([0,2,8], -6), ([0,2,9], -4), ([0,2,10], -4), ([0,2,11], -4), ([0,3,3], -2), ([0,3,4], -4), ([0,3,5], -4), ([0,3,6], -8), ([0,3,7], -6), ([0,3,8], -6), ([0,3,9], -4), ([0,3,10], -4), ([0,3,11], -4), ([0,4,4], -2), ([0,4,5], -4), ([0,4,6], -8), ([0,4,7], -6), ([0,4,8], -6), ([0,4,9], -4), ([0,4,10], -4), ([0,4,11], -4), ([0,5,5], -2), ([0,5,6], -8), ([0,5,7], -6), ([0,5,8], -6), ([0,5,9], -4), ([0,5,10], -4), ([0,5,11], -4), ([0,6,6], -6), ([0,6,7], -10), ([0,6,8], -10), ([0,6,9], -8), ([0,6,10], -4), ([0,6,11], -4), ([0,7,7], -4), ([0,7,8], -8), ([0,7,9], -8), ([0,7,10], -4), ([0,7,11], -4), ([0,8,8], -4), ([0,8,9], -8), ([0,8,10], -4), ([0,8,11], -4), ([0,9,9], -4), ([0,9,10], -4), ([0,9,11], -4), ([1,1,2], -2), ([1,1,3], -2), ([1,1,4], -2), ([1,1,5], -2), ([1,1,6], -4), ([1,1,7], -2), ([1,1,8], -4), ([1,1,9], -4), ([1,1,10], -4), ([1,1,11], -4), ([1,2,2], -4), ([1,2,3], -8), ([1,2,4], -8), ([1,2,5], -8), ([1,2,6], -12), ([1,2,7], -8), ([1,2,8], -12), ([1,2,9], -10), ([1,2,10], -8), ([1,2,11], -8), ([1,3,3], -4), ([1,3,4], -8), ([1,3,5], -8), ([1,3,6], -12), ([1,3,7], -8), ([1,3,8], -12), ([1,3,9], -10), ([1,3,10], -8), ([1,3,11], -8), ([1,4,4], -4), ([1,4,5], -8), ([1,4,6], -12), ([1,4,7], -8), ([1,4,8], -12), ([1,4,9], -10), ([1,4,10], -8), ([1,4,11], -8), ([1,5,5], -4), ([1,5,6], -12), ([1,5,7], -8), ([1,5,8], -12), ([1,5,9], -10), ([1,5,10], -8), ([1,5,11], -8), ([1,6,6], -8), ([1,6,7], -12), ([1,6,8], -16), ([1,6,9], -14), ([1,6,10], -8), ([1,6,11], -8), ([1,7,7], -4), ([1,7,8], -12), ([1,7,9], -12), ([1,7,10], -8), ([1,7,11], -8), ([1,8,8], -8), ([1,8,9], -12), ([1,8,10], -8), ([1,8,11], -8), ([1,9,9], -4), ([1,9,10], -4), ([1,9,11], -4), ([2,2,2], -2), ([2,2,3], -6), ([2,2,4], -6), ([2,2,5], -6), ([2,2,6], -8), ([2,2,7], -6), ([2,2,8], -8), ([2,2,9], -6), ([2,2,10], -4), ([2,2,11], -6), ([2,3,3], -6), ([2,3,4], -12), ([2,3,5], -12), ([2,3,6], -16), ([2,3,7], -12), ([2,3,8], -16), ([2,3,9], -12), ([2,3,10], -8), ([2,3,11], -12), ([2,4,4], -6), ([2,4,5], -12), ([2,4,6], -16), ([2,4,7], -12), ([2,4,8], -16), ([2,4,9], -12), ([2,4,10], -8), ([2,4,11], -12), ([2,5,5], -6), ([2,5,6], -16), ([2,5,7], -12), ([2,5,8], -16), ([2,5,9], -12), ([2,5,10], -8), ([2,5,11], -12), ([2,6,6], -10), ([2,6,7], -16), ([2,6,8], -20), ([2,6,9], -16), ([2,6,10], -8), ([2,6,11], -12), ([2,7,7], -6), ([2,7,8], -16), ([2,7,9], -14), ([2,7,10], -8), ([2,7,11], -8), ([2,8,8], -10), ([2,8,9], -14), ([2,8,10], -8), ([2,8,11], -8), ([2,9,9], -4), ([2,9,10], -4), ([2,9,11], -4), ([3,3,3], -2), ([3,3,4], -6), ([3,3,5], -6), ([3,3,6], -8), ([3,3,7], -6), ([3,3,8], -8), ([3,3,9], -6), ([3,3,10], -4), ([3,3,11], -6), ([3,4,4], -6), ([3,4,5], -12), ([3,4,6], -16), ([3,4,7], -12), ([3,4,8], -16), ([3,4,9], -12), ([3,4,10], -8), ([3,4,11], -12), ([3,5,5], -6), ([3,5,6], -16), ([3,5,7], -12), ([3,5,8], -16), ([3,5,9], -12), ([3,5,10], -8), ([3,5,11], -12), ([3,6,6], -10), ([3,6,7], -16), ([3,6,8], -20), ([3,6,9], -16), ([3,6,10], -8), ([3,6,11], -12), ([3,7,7], -6), ([3,7,8], -16), ([3,7,9], -14), ([3,7,10], -8), ([3,7,11], -8), ([3,8,8], -10), ([3,8,9], -14), ([3,8,10], -8), ([3,8,11], -8), ([3,9,9], -4), ([3,9,10], -4), ([3,9,11], -4), ([4,4,4], -2), ([4,4,5], -6), ([4,4,6], -8), ([4,4,7], -6), ([4,4,8], -8), ([4,4,9], -6), ([4,4,10], -4), ([4,4,11], -6), ([4,5,5], -6), ([4,5,6], -16), ([4,5,7], -12), ([4,5,8], -16), ([4,5,9], -12), ([4,5,10], -8), ([4,5,11], -12), ([4,6,6], -10), ([4,6,7], -16), ([4,6,8], -20), ([4,6,9], -16), ([4,6,10], -8), ([4,6,11], -12), ([4,7,7], -6), ([4,7,8], -16), ([4,7,9], -14), ([4,7,10], -8), ([4,7,11], -8), ([4,8,8], -10), ([4,8,9], -14), ([4,8,10], -8), ([4,8,11], -8), ([4,9,9], -4), ([4,9,10], -4), ([4,9,11], -4), ([5,5,5], -2), ([5,5,6], -8), ([5,5,7], -6), ([5,5,8], -8), ([5,5,9], -6), ([5,5,10], -4), ([5,5,11], -6), ([5,6,6], -10), ([5,6,7], -16), ([5,6,8], -20), ([5,6,9], -16), ([5,6,10], -8), ([5,6,11], -12), ([5,7,7], -6), ([5,7,8], -16), ([5,7,9], -14), ([5,7,10], -8), ([5,7,11], -8), ([5,8,8], -10), ([5,8,9], -14), ([5,8,10], -8), ([5,8,11], -8), ([5,9,9], -4), ([5,9,10], -4), ([5,9,11], -4), ([6,6,6], -4), ([6,6,7], -10), ([6,6,8], -12), ([6,6,9], -10), ([6,6,10], -4), ([6,6,11], -6), ([6,7,7], -8), ([6,7,8], -20), ([6,7,9], -18), ([6,7,10], -8), ([6,7,11], -8), ([6,8,8], -12), ([6,8,9], -18), ([6,8,10], -8), ([6,9,9], -6), ([6,9,10], -4), ([6,9,11], 4), ([6,10,11], 8), ([6,11,11], 8), ([7,7,7], -2), ([7,7,8], -8), ([7,7,9], -8), ([7,7,10], -4), ([7,7,11], -4), ([7,8,8], -10), ([7,8,9], -16), ([7,8,10], -8), ([7,9,9], -6), ([7,9,10], -4), ([7,9,11], 4), ([7,10,11], 8), ([7,11,11], 8), ([8,8,8], -4), ([8,8,9], -8), ([8,8,10], -4), ([8,8,11], 4), ([8,9,9], -6), ([8,9,10], -4), ([8,9,11], 12), ([8,10,11], 16), ([8,11,11], 16), ([9,9,9], -2), ([9,9,10], -2), ([9,9,11], 6), ([9,10,11], 16), ([9,11,11], 16), ([10,10,11], 8), ([10,11,11], 16), ([11,11,11], 8)]
theorem atom0341_data : atom0341 = SparsePolynomial.monoTimes [] 1 base03 := by decide +kernel
theorem eval_atom0341 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0341 = (detB (outer g)) := by
  rw [atom0341_data, SparsePolynomial.eval_monoTimes, eval_base03]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0341_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12480 : Int) atom0341) := by
  rw [SparsePolynomial.eval_scale, eval_atom0341]
  have hb := base03_nonneg g hg hA hB
  rw [eval_base03] at hb
  have ht : 0 ≤ (detB (outer g)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0342 : SparsePolynomial.Poly := [([0,0,0], -1), ([0,0,1], -2), ([0,0,2], -2), ([0,0,3], -2), ([0,0,4], -2), ([0,0,5], -2), ([0,0,6], -2), ([0,0,7], -2), ([0,0,8], -2), ([0,0,9], -2), ([0,1,1], -1), ([0,1,2], -2), ([0,1,3], -2), ([0,1,4], -2), ([0,1,5], -2), ([0,1,6], -2), ([0,1,7], -2), ([0,1,8], -2), ([0,1,9], -2), ([0,2,2], -1), ([0,2,3], -2), ([0,2,4], -2), ([0,2,5], -2), ([0,2,6], -2), ([0,2,7], -2), ([0,2,8], -2), ([0,2,9], -2), ([0,3,3], -1), ([0,3,4], -2), ([0,3,5], -2), ([0,3,6], -2), ([0,3,7], -2), ([0,3,8], -2), ([0,3,9], -2), ([0,4,4], -1), ([0,4,5], -2), ([0,4,6], -2), ([0,4,7], -2), ([0,4,8], -2), ([0,4,9], -2), ([0,5,5], -1), ([0,5,6], -2), ([0,5,7], -2), ([0,5,8], -2), ([0,5,9], -2), ([0,6,6], -1), ([0,6,7], -2), ([0,6,8], -2), ([0,6,9], -2), ([0,7,7], -1), ([0,7,8], -2), ([0,7,9], -2), ([0,8,8], -1), ([0,8,9], -2), ([0,8,11], 4), ([0,9,9], -1), ([0,9,11], 4), ([0,10,11], 4), ([0,11,11], 4)]
theorem atom0342_data : atom0342 = SparsePolynomial.monoTimes [0] 1 base04 := by decide +kernel
theorem eval_atom0342 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0342 = (minorB (outer g) 0 1 * g 0) := by
  rw [atom0342_data, SparsePolynomial.eval_monoTimes, eval_base04]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0342_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4224 : Int) atom0342) := by
  rw [SparsePolynomial.eval_scale, eval_atom0342]
  have hg0 : 0 ≤ g 0 := hg 0
  have hb := base04_nonneg g hg hA hB
  rw [eval_base04] at hb
  have ht : 0 ≤ (minorB (outer g) 0 1 * g 0) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0343 : SparsePolynomial.Poly := [([0,0,11], -2), ([0,1,11], -2), ([0,2,11], -2), ([0,3,11], -2), ([0,4,11], -2), ([0,5,11], -2), ([0,6,11], -2), ([0,7,11], -2), ([0,10,11], 2), ([0,11,11], 4)]
theorem atom0343_data : atom0343 = SparsePolynomial.monoTimes [0,11] 1 base05 := by decide +kernel
theorem eval_atom0343 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0343 = (quadB (outer g) ![1,1,0] * g 0 * g 11) := by
  rw [atom0343_data, SparsePolynomial.eval_monoTimes, eval_base05]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0343_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5280 : Int) atom0343) := by
  rw [SparsePolynomial.eval_scale, eval_atom0343]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base05_nonneg g hg hA hB
  rw [eval_base05] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,1,0] * g 0 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0344 : SparsePolynomial.Poly := [([0,2,10], -4), ([1,2,10], -8), ([2,2,10], -16), ([2,3,10], -16), ([2,4,10], -16), ([2,5,10], -16), ([2,6,10], -8), ([2,8,10], 8), ([2,9,10], 12), ([2,10,10], 16), ([2,10,11], 18)]
theorem atom0344_data : atom0344 = SparsePolynomial.monoTimes [2,10] 1 base06 := by decide +kernel
theorem eval_atom0344 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0344 = (quadB (outer g) ![1,2,2] * g 2 * g 10) := by
  rw [atom0344_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0344_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1332 : Int) atom0344) := by
  rw [SparsePolynomial.eval_scale, eval_atom0344]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 2 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0345 : SparsePolynomial.Poly := [([0,3,4], -4), ([1,3,4], -8), ([2,3,4], -16), ([3,3,4], -16), ([3,4,4], -16), ([3,4,5], -16), ([3,4,6], -8), ([3,4,8], 8), ([3,4,9], 12), ([3,4,10], 16), ([3,4,11], 18)]
theorem atom0345_data : atom0345 = SparsePolynomial.monoTimes [3,4] 1 base06 := by decide +kernel
theorem eval_atom0345 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0345 = (quadB (outer g) ![1,2,2] * g 3 * g 4) := by
  rw [atom0345_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0345_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (264 : Int) atom0345) := by
  rw [SparsePolynomial.eval_scale, eval_atom0345]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0346 : SparsePolynomial.Poly := [([0,3,10], -4), ([1,3,10], -8), ([2,3,10], -16), ([3,3,10], -16), ([3,4,10], -16), ([3,5,10], -16), ([3,6,10], -8), ([3,8,10], 8), ([3,9,10], 12), ([3,10,10], 16), ([3,10,11], 18)]
theorem atom0346_data : atom0346 = SparsePolynomial.monoTimes [3,10] 1 base06 := by decide +kernel
theorem eval_atom0346 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0346 = (quadB (outer g) ![1,2,2] * g 3 * g 10) := by
  rw [atom0346_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0346_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2187 : Int) atom0346) := by
  rw [SparsePolynomial.eval_scale, eval_atom0346]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 3 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0347 : SparsePolynomial.Poly := [([0,4,5], -4), ([1,4,5], -8), ([2,4,5], -16), ([3,4,5], -16), ([4,4,5], -16), ([4,5,5], -16), ([4,5,6], -8), ([4,5,8], 8), ([4,5,9], 12), ([4,5,10], 16), ([4,5,11], 18)]
theorem atom0347_data : atom0347 = SparsePolynomial.monoTimes [4,5] 1 base06 := by decide +kernel
theorem eval_atom0347 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0347 = (quadB (outer g) ![1,2,2] * g 4 * g 5) := by
  rw [atom0347_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0347_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1644 : Int) atom0347) := by
  rw [SparsePolynomial.eval_scale, eval_atom0347]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0348 : SparsePolynomial.Poly := [([0,4,7], -4), ([1,4,7], -8), ([2,4,7], -16), ([3,4,7], -16), ([4,4,7], -16), ([4,5,7], -16), ([4,6,7], -8), ([4,7,8], 8), ([4,7,9], 12), ([4,7,10], 16), ([4,7,11], 18)]
theorem atom0348_data : atom0348 = SparsePolynomial.monoTimes [4,7] 1 base06 := by decide +kernel
theorem eval_atom0348 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0348 = (quadB (outer g) ![1,2,2] * g 4 * g 7) := by
  rw [atom0348_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0348_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (552 : Int) atom0348) := by
  rw [SparsePolynomial.eval_scale, eval_atom0348]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0349 : SparsePolynomial.Poly := [([0,4,10], -4), ([1,4,10], -8), ([2,4,10], -16), ([3,4,10], -16), ([4,4,10], -16), ([4,5,10], -16), ([4,6,10], -8), ([4,8,10], 8), ([4,9,10], 12), ([4,10,10], 16), ([4,10,11], 18)]
theorem atom0349_data : atom0349 = SparsePolynomial.monoTimes [4,10] 1 base06 := by decide +kernel
theorem eval_atom0349 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0349 = (quadB (outer g) ![1,2,2] * g 4 * g 10) := by
  rw [atom0349_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0349_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2148 : Int) atom0349) := by
  rw [SparsePolynomial.eval_scale, eval_atom0349]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 4 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0350 : SparsePolynomial.Poly := [([0,5,7], -4), ([1,5,7], -8), ([2,5,7], -16), ([3,5,7], -16), ([4,5,7], -16), ([5,5,7], -16), ([5,6,7], -8), ([5,7,8], 8), ([5,7,9], 12), ([5,7,10], 16), ([5,7,11], 18)]
theorem atom0350_data : atom0350 = SparsePolynomial.monoTimes [5,7] 1 base06 := by decide +kernel
theorem eval_atom0350 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0350 = (quadB (outer g) ![1,2,2] * g 5 * g 7) := by
  rw [atom0350_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0350_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1152 : Int) atom0350) := by
  rw [SparsePolynomial.eval_scale, eval_atom0350]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0351 : SparsePolynomial.Poly := [([0,5,10], -4), ([1,5,10], -8), ([2,5,10], -16), ([3,5,10], -16), ([4,5,10], -16), ([5,5,10], -16), ([5,6,10], -8), ([5,8,10], 8), ([5,9,10], 12), ([5,10,10], 16), ([5,10,11], 18)]
theorem atom0351_data : atom0351 = SparsePolynomial.monoTimes [5,10] 1 base06 := by decide +kernel
theorem eval_atom0351 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0351 = (quadB (outer g) ![1,2,2] * g 5 * g 10) := by
  rw [atom0351_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0351_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1260 : Int) atom0351) := by
  rw [SparsePolynomial.eval_scale, eval_atom0351]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 5 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0352 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -16), ([0,1,4], -16), ([0,1,5], -16), ([0,1,6], -14), ([0,1,7], -10), ([0,1,8], -2), ([0,1,9], 2), ([0,1,10], 10), ([0,1,11], 18)]
theorem atom0352_data : atom0352 = SparsePolynomial.monoTimes [0,1] 1 base07 := by decide +kernel
theorem eval_atom0352 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0352 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0352_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0352_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (936 : Int) atom0352) := by
  rw [SparsePolynomial.eval_scale, eval_atom0352]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0353 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -16), ([0,2,4], -16), ([0,2,5], -16), ([0,2,6], -14), ([0,2,7], -10), ([0,2,8], -2), ([0,2,9], 2), ([0,2,10], 10), ([0,2,11], 18)]
theorem atom0353_data : atom0353 = SparsePolynomial.monoTimes [0,2] 1 base07 := by decide +kernel
theorem eval_atom0353 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0353 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0353_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0353_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1344 : Int) atom0353) := by
  rw [SparsePolynomial.eval_scale, eval_atom0353]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0354 : SparsePolynomial.Poly := [([0,0,3], -8), ([0,1,3], -12), ([0,2,3], -16), ([0,3,3], -16), ([0,3,4], -16), ([0,3,5], -16), ([0,3,6], -14), ([0,3,7], -10), ([0,3,8], -2), ([0,3,9], 2), ([0,3,10], 10), ([0,3,11], 18)]
theorem atom0354_data : atom0354 = SparsePolynomial.monoTimes [0,3] 1 base07 := by decide +kernel
theorem eval_atom0354 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0354 = (quadB (outer g) ![2,2,1] * g 0 * g 3) := by
  rw [atom0354_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0354_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1752 : Int) atom0354) := by
  rw [SparsePolynomial.eval_scale, eval_atom0354]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0355 : SparsePolynomial.Poly := [([0,0,4], -8), ([0,1,4], -12), ([0,2,4], -16), ([0,3,4], -16), ([0,4,4], -16), ([0,4,5], -16), ([0,4,6], -14), ([0,4,7], -10), ([0,4,8], -2), ([0,4,9], 2), ([0,4,10], 10), ([0,4,11], 18)]
theorem atom0355_data : atom0355 = SparsePolynomial.monoTimes [0,4] 1 base07 := by decide +kernel
theorem eval_atom0355 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0355 = (quadB (outer g) ![2,2,1] * g 0 * g 4) := by
  rw [atom0355_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0355_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2160 : Int) atom0355) := by
  rw [SparsePolynomial.eval_scale, eval_atom0355]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0356 : SparsePolynomial.Poly := [([0,0,5], -8), ([0,1,5], -12), ([0,2,5], -16), ([0,3,5], -16), ([0,4,5], -16), ([0,5,5], -16), ([0,5,6], -14), ([0,5,7], -10), ([0,5,8], -2), ([0,5,9], 2), ([0,5,10], 10), ([0,5,11], 18)]
theorem atom0356_data : atom0356 = SparsePolynomial.monoTimes [0,5] 1 base07 := by decide +kernel
theorem eval_atom0356 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0356 = (quadB (outer g) ![2,2,1] * g 0 * g 5) := by
  rw [atom0356_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0356_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2568 : Int) atom0356) := by
  rw [SparsePolynomial.eval_scale, eval_atom0356]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0357 : SparsePolynomial.Poly := [([0,0,10], -8), ([0,1,10], -12), ([0,2,10], -16), ([0,3,10], -16), ([0,4,10], -16), ([0,5,10], -16), ([0,6,10], -14), ([0,7,10], -10), ([0,8,10], -2), ([0,9,10], 2), ([0,10,10], 10), ([0,10,11], 18)]
theorem atom0357_data : atom0357 = SparsePolynomial.monoTimes [0,10] 1 base07 := by decide +kernel
theorem eval_atom0357 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0357 = (quadB (outer g) ![2,2,1] * g 0 * g 10) := by
  rw [atom0357_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0357_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (912 : Int) atom0357) := by
  rw [SparsePolynomial.eval_scale, eval_atom0357]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0358 : SparsePolynomial.Poly := [([0,1,11], -8), ([1,1,11], -12), ([1,2,11], -16), ([1,3,11], -16), ([1,4,11], -16), ([1,5,11], -16), ([1,6,11], -14), ([1,7,11], -10), ([1,8,11], -2), ([1,9,11], 2), ([1,10,11], 10), ([1,11,11], 18)]
theorem atom0358_data : atom0358 = SparsePolynomial.monoTimes [1,11] 1 base07 := by decide +kernel
theorem eval_atom0358 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0358 = (quadB (outer g) ![2,2,1] * g 1 * g 11) := by
  rw [atom0358_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0358_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (596 : Int) atom0358) := by
  rw [SparsePolynomial.eval_scale, eval_atom0358]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0359 : SparsePolynomial.Poly := [([0,2,11], -8), ([1,2,11], -12), ([2,2,11], -16), ([2,3,11], -16), ([2,4,11], -16), ([2,5,11], -16), ([2,6,11], -14), ([2,7,11], -10), ([2,8,11], -2), ([2,9,11], 2), ([2,10,11], 10), ([2,11,11], 18)]
theorem atom0359_data : atom0359 = SparsePolynomial.monoTimes [2,11] 1 base07 := by decide +kernel
theorem eval_atom0359 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0359 = (quadB (outer g) ![2,2,1] * g 2 * g 11) := by
  rw [atom0359_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0359_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (408 : Int) atom0359) := by
  rw [SparsePolynomial.eval_scale, eval_atom0359]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 2 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0360 : SparsePolynomial.Poly := [([0,4,4], -8), ([1,4,4], -12), ([2,4,4], -16), ([3,4,4], -16), ([4,4,4], -16), ([4,4,5], -16), ([4,4,6], -14), ([4,4,7], -10), ([4,4,8], -2), ([4,4,9], 2), ([4,4,10], 10), ([4,4,11], 18)]
theorem atom0360_data : atom0360 = SparsePolynomial.monoTimes [4,4] 1 base07 := by decide +kernel
theorem eval_atom0360 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0360 = (quadB (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0360_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0360_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1248 : Int) atom0360) := by
  rw [SparsePolynomial.eval_scale, eval_atom0360]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0361 : SparsePolynomial.Poly := [([0,5,5], -8), ([1,5,5], -12), ([2,5,5], -16), ([3,5,5], -16), ([4,5,5], -16), ([5,5,5], -16), ([5,5,6], -14), ([5,5,7], -10), ([5,5,8], -2), ([5,5,9], 2), ([5,5,10], 10), ([5,5,11], 18)]
theorem atom0361_data : atom0361 = SparsePolynomial.monoTimes [5,5] 1 base07 := by decide +kernel
theorem eval_atom0361 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0361 = (quadB (outer g) ![2,2,1] * g 5 * g 5) := by
  rw [atom0361_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0361_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1728 : Int) atom0361) := by
  rw [SparsePolynomial.eval_scale, eval_atom0361]
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 5 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0362 : SparsePolynomial.Poly := [([0,7,7], -8), ([1,7,7], -12), ([2,7,7], -16), ([3,7,7], -16), ([4,7,7], -16), ([5,7,7], -16), ([6,7,7], -14), ([7,7,7], -10), ([7,7,8], -2), ([7,7,9], 2), ([7,7,10], 10), ([7,7,11], 18)]
theorem atom0362_data : atom0362 = SparsePolynomial.monoTimes [7,7] 1 base07 := by decide +kernel
theorem eval_atom0362 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0362 = (quadB (outer g) ![2,2,1] * g 7 * g 7) := by
  rw [atom0362_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, variables]
  <;> ring
theorem atom0362_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1728 : Int) atom0362) := by
  rw [SparsePolynomial.eval_scale, eval_atom0362]
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def block004 : SparsePolynomial.Poly := [([0,0,0], -4224), ([0,0,1], -15936), ([0,0,2], -19200), ([0,0,3], -22464), ([0,0,4], -25728), ([0,0,5], -28992), ([0,0,6], -46464), ([0,0,7], -46464), ([0,0,8], -46464), ([0,0,9], -46464), ([0,0,10], -45312), ([0,0,11], -48576), ([0,1,1], -25440), ([0,1,2], -77568), ([0,1,3], -82464), ([0,1,4], -87360), ([0,1,5], -92768), ([0,1,6], -135600), ([0,1,7], -99280), ([0,1,8], -86352), ([0,1,9], -82800), ([0,1,10], -82352), ([0,1,11], -81408), ([0,2,2], -63744), ([0,2,3], -134016), ([0,2,4], -140544), ([0,2,5], -147072), ([0,2,6], -179328), ([0,2,7], -135936), ([0,2,8], -112128), ([0,2,9], -81792), ([0,2,10], -82512), ([0,2,11], -65664), ([0,3,3], -73056), ([0,3,4], -148128), ([0,3,5], -153600), ([0,3,6], -185040), ([0,3,7], -140016), ([0,3,8], -112944), ([0,3,9], -80976), ([0,3,10], -81852), ([0,3,11], -55056), ([0,4,4], -86784), ([0,4,5], -166704), ([0,4,6], -190752), ([0,4,7], -146304), ([0,4,8], -113760), ([0,4,9], -80160), ([0,4,10], -77616), ([0,4,11], -47712), ([0,5,5], -97152), ([0,5,6], -196464), ([0,5,7], -152784), ([0,5,8], -114576), ([0,5,9], -79344), ([0,5,10], -69984), ([0,5,11], -40368), ([0,6,6], -118272), ([0,6,7], -198528), ([0,6,8], -185472), ([0,6,9], -160512), ([0,6,10], -88800), ([0,6,11], -86592), ([0,7,7], -94080), ([0,7,8], -160512), ([0,7,9], -160512), ([0,7,10], -85152), ([0,7,11], -86592), ([0,8,8], -80256), ([0,8,9], -160512), ([0,8,10], -77856), ([0,8,11], -59136), ([0,9,9], -80256), ([0,9,10], -74208), ([0,9,11], -59136), ([0,10,10], 9120), ([0,10,11], 43872), ([0,11,11], 38016), ([1,1,1], -14976), ([1,1,2], -57984), ([1,1,3], -57984), ([1,1,4], -57984), ([1,1,5], -59520), ([1,1,6], -93504), ([1,1,7], -66816), ([1,1,8], -70464), ([1,1,9], -74112), ([1,1,10], -77760), ([1,1,11], -81408), ([1,2,2], -76032), ([1,2,3], -152064), ([1,2,4], -152064), ([1,2,5], -154112), ([1,2,6], -228096), ([1,2,7], -173824), ([1,2,8], -188928), ([1,2,9], -190848), ([1,2,10], -181664), ([1,2,11], -194080), ([1,3,3], -84384), ([1,3,4], -154176), ([1,3,5], -154112), ([1,3,6], -228096), ([1,3,7], -173824), ([1,3,8], -188928), ([1,3,9], -190848), ([1,3,10], -188504), ([1,3,11], -189184), ([1,4,4], -91008), ([1,4,5], -167264), ([1,4,6], -228096), ([1,4,7], -178240), ([1,4,8], -188928), ([1,4,9], -190848), ([1,4,10], -188192), ([1,4,11], -189184), ([1,5,5], -98816), ([1,5,6], -229120), ([1,5,7], -183552), ([1,5,8], -188416), ([1,5,9], -190080), ([1,5,10], -179808), ([1,5,11], -186880), ([1,6,6], -152064), ([1,6,7], -238976), ([1,6,8], -264960), ([1,6,9], -266496), ([1,6,10], -161536), ([1,6,11], -174200), ([1,7,7], -102208), ([1,7,8], -196544), ([1,7,9], -220128), ([1,7,10], -143200), ([1,7,11], -140440), ([1,8,8], -125952), ([1,8,9], -201792), ([1,8,10], -121216), ([1,8,11], -120248), ([1,9,9], -75744), ([1,9,10], -68448), ([1,9,11], -63632), ([1,10,10], 11840), ([1,10,11], 44512), ([1,11,11], 41760), ([2,2,2], -38016), ([2,2,3], -114048), ([2,2,4], -114048), ([2,2,5], -114048), ([2,2,6], -152064), ([2,2,7], -114048), ([2,2,8], -125952), ([2,2,9], -114048), ([2,2,10], -97344), ([2,2,11], -120576), ([2,3,3], -125184), ([2,3,4], -232320), ([2,3,5], -228096), ([2,3,6], -304128), ([2,3,7], -228096), ([2,3,8], -251904), ([2,3,9], -228096), ([2,3,10], -208368), ([2,3,11], -234624), ([2,4,4], -134016), ([2,4,5], -254400), ([2,4,6], -304128), ([2,4,7], -236928), ([2,4,8], -251904), ([2,4,9], -228096), ([2,4,10], -207744), ([2,4,11], -234624), ([2,5,5], -141696), ([2,5,6], -304128), ([2,5,7], -246528), ([2,5,8], -251904), ([2,5,9], -228096), ([2,5,10], -193536), ([2,5,11], -234624), ([2,6,6], -190080), ([2,6,7], -304128), ([2,6,8], -327936), ([2,6,9], -304128), ([2,6,10], -162720), ([2,6,11], -233808), ([2,7,7], -141696), ([2,7,8], -264960), ([2,7,9], -266112), ([2,7,10], -152064), ([2,7,11], -156144), ([2,8,8], -150912), ([2,8,9], -226944), ([2,8,10], -115296), ([2,8,11], -126768), ([2,9,9], -76032), ([2,9,10], -60048), ([2,9,11], -75216), ([2,10,10], 21312), ([2,10,11], 28056), ([2,11,11], 7344), ([3,3,3], -49152), ([3,3,4], -129408), ([3,3,5], -125184), ([3,3,6], -157632), ([3,3,7], -116832), ([3,3,8], -123168), ([3,3,9], -109872), ([3,3,10], -104064), ([3,3,11], -101520), ([3,4,4], -138240), ([3,4,5], -258624), ([3,4,6], -306240), ([3,4,7], -236928), ([3,4,8], -249792), ([3,4,9], -224928), ([3,4,10], -217200), ([3,4,11], -223344), ([3,5,5], -141696), ([3,5,6], -304128), ([3,5,7], -246528), ([3,5,8], -251904), ([3,5,9], -228096), ([3,5,10], -207216), ([3,5,11], -228096), ([3,6,6], -190080), ([3,6,7], -304128), ([3,6,8], -327936), ([3,6,9], -304128), ([3,6,10], -169560), ([3,6,11], -228096), ([3,7,7], -141696), ([3,7,8], -264960), ([3,7,9], -266112), ([3,7,10], -152064), ([3,7,11], -152064), ([3,8,8], -150912), ([3,8,9], -226944), ([3,8,10], -108456), ([3,8,11], -125952), ([3,9,9], -76032), ([3,9,10], -49788), ([3,9,11], -76032), ([3,10,10], 34992), ([3,10,11], 39366), ([4,4,4], -57984), ([4,4,5], -160320), ([4,4,6], -169536), ([4,4,7], -135360), ([4,4,8], -128448), ([4,4,9], -111552), ([4,4,10], -97920), ([4,4,11], -91584), ([4,5,5], -168000), ([4,5,6], -317280), ([4,5,7], -255360), ([4,5,8], -238752), ([4,5,9], -208368), ([4,5,10], -180288), ([4,5,11], -198504), ([4,6,6], -190080), ([4,6,7], -308544), ([4,6,8], -327936), ([4,6,9], -304128), ([4,6,10], -169248), ([4,6,11], -228096), ([4,7,7], -141696), ([4,7,8], -260544), ([4,7,9], -259488), ([4,7,10], -143232), ([4,7,11], -142128), ([4,8,8], -150912), ([4,8,9], -226944), ([4,8,10], -108768), ([4,8,11], -125952), ([4,9,9], -76032), ([4,9,10], -50256), ([4,9,11], -76032), ([4,10,10], 34368), ([4,10,11], 38664), ([5,5,5], -65664), ([5,5,6], -176256), ([5,5,7], -149760), ([5,5,8], -129408), ([5,5,9], -110592), ([5,5,10], -78912), ([5,5,11], -82944), ([5,6,6], -190080), ([5,6,7], -313344), ([5,6,8], -327936), ([5,6,9], -304128), ([5,6,10], -162144), ([5,6,11], -228096), ([5,7,7], -141696), ([5,7,8], -255744), ([5,7,9], -252288), ([5,7,10], -133632), ([5,7,11], -131328), ([5,8,8], -150912), ([5,8,9], -226944), ([5,8,10], -115872), ([5,8,11], -125952), ([5,9,9], -76032), ([5,9,10], -60912), ([5,9,11], -76032), ([5,10,10], 20160), ([5,10,11], 22680), ([6,6,6], -76032), ([6,6,7], -190080), ([6,6,8], -201984), ([6,6,9], -190080), ([6,6,10], -76032), ([6,6,11], -114048), ([6,7,7], -176256), ([6,7,8], -340992), ([6,7,9], -342144), ([6,7,10], -152064), ([6,7,11], -152064), ([6,8,8], -188928), ([6,8,9], -302976), ([6,8,10], -125952), ([6,8,11], -26112), ([6,9,9], -114048), ([6,9,10], -76032), ([6,9,11], 76032), ([6,10,11], 152064), ([6,11,11], 152064), ([7,7,7], -55296), ([7,7,8], -142464), ([7,7,9], -148608), ([7,7,10], -58752), ([7,7,11], -44928), ([7,8,8], -163968), ([7,8,9], -278016), ([7,8,10], -125952), ([7,8,11], -26112), ([7,9,9], -114048), ([7,9,10], -76032), ([7,9,11], 76032), ([7,10,11], 152064), ([7,11,11], 152064), ([8,8,8], -62976), ([8,8,9], -139008), ([8,8,10], -62976), ([8,8,11], 36864), ([8,9,9], -114048), ([8,9,10], -76032), ([8,9,11], 400896), ([8,10,10], 171072), ([8,10,11], 542592), ([8,11,11], 342144), ([9,9,9], 9600), ([9,9,10], 125760), ([9,9,11], 222720), ([9,10,10], 190080), ([9,10,11], 602880), ([9,11,11], 380160), ([10,10,10], 69696), ([10,10,11], 331584), ([10,11,11], 418176), ([11,11,11], 152064)]
theorem block004_data : block004 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (225024 : Int) atom0320) (SparsePolynomial.scale (171072 : Int) atom0321)) (SparsePolynomial.merge (SparsePolynomial.scale (290688 : Int) atom0322) (SparsePolynomial.merge (SparsePolynomial.scale (90240 : Int) atom0323) (SparsePolynomial.scale (47616 : Int) atom0324)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (163776 : Int) atom0325) (SparsePolynomial.scale (108672 : Int) atom0326)) (SparsePolynomial.merge (SparsePolynomial.scale (190080 : Int) atom0327) (SparsePolynomial.merge (SparsePolynomial.scale (298752 : Int) atom0328) (SparsePolynomial.scale (76032 : Int) atom0329))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (69696 : Int) atom0330) (SparsePolynomial.scale (179520 : Int) atom0331)) (SparsePolynomial.merge (SparsePolynomial.scale (114048 : Int) atom0332) (SparsePolynomial.merge (SparsePolynomial.scale (6528 : Int) atom0333) (SparsePolynomial.scale (128 : Int) atom0334)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1360 : Int) atom0335) (SparsePolynomial.merge (SparsePolynomial.scale (48 : Int) atom0336) (SparsePolynomial.scale (1184 : Int) atom0337))) (SparsePolynomial.merge (SparsePolynomial.scale (1724 : Int) atom0338) (SparsePolynomial.merge (SparsePolynomial.scale (696 : Int) atom0339) (SparsePolynomial.scale (1248 : Int) atom0340)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12480 : Int) atom0341) (SparsePolynomial.scale (4224 : Int) atom0342)) (SparsePolynomial.merge (SparsePolynomial.scale (5280 : Int) atom0343) (SparsePolynomial.merge (SparsePolynomial.scale (1332 : Int) atom0344) (SparsePolynomial.scale (264 : Int) atom0345)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2187 : Int) atom0346) (SparsePolynomial.merge (SparsePolynomial.scale (1644 : Int) atom0347) (SparsePolynomial.scale (552 : Int) atom0348))) (SparsePolynomial.merge (SparsePolynomial.scale (2148 : Int) atom0349) (SparsePolynomial.merge (SparsePolynomial.scale (1152 : Int) atom0350) (SparsePolynomial.scale (1260 : Int) atom0351))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (936 : Int) atom0352) (SparsePolynomial.scale (1344 : Int) atom0353)) (SparsePolynomial.merge (SparsePolynomial.scale (1752 : Int) atom0354) (SparsePolynomial.merge (SparsePolynomial.scale (2160 : Int) atom0355) (SparsePolynomial.scale (2568 : Int) atom0356)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (912 : Int) atom0357) (SparsePolynomial.merge (SparsePolynomial.scale (596 : Int) atom0358) (SparsePolynomial.scale (408 : Int) atom0359))) (SparsePolynomial.merge (SparsePolynomial.scale (1248 : Int) atom0360) (SparsePolynomial.merge (SparsePolynomial.scale (1728 : Int) atom0361) (SparsePolynomial.scale (1728 : Int) atom0362))))))) := by decide +kernel
theorem block004_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block004 := by
  rw [block004_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0320_nonneg g hg hA hB) (atom0321_nonneg g hg hA hB)) (add_nonneg (atom0322_nonneg g hg hA hB) (add_nonneg (atom0323_nonneg g hg hA hB) (atom0324_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0325_nonneg g hg hA hB) (atom0326_nonneg g hg hA hB)) (add_nonneg (atom0327_nonneg g hg hA hB) (add_nonneg (atom0328_nonneg g hg hA hB) (atom0329_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0330_nonneg g hg hA hB) (atom0331_nonneg g hg hA hB)) (add_nonneg (atom0332_nonneg g hg hA hB) (add_nonneg (atom0333_nonneg g hg hA hB) (atom0334_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0335_nonneg g hg hA hB) (add_nonneg (atom0336_nonneg g hg hA hB) (atom0337_nonneg g hg hA hB))) (add_nonneg (atom0338_nonneg g hg hA hB) (add_nonneg (atom0339_nonneg g hg hA hB) (atom0340_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0341_nonneg g hg hA hB) (atom0342_nonneg g hg hA hB)) (add_nonneg (atom0343_nonneg g hg hA hB) (add_nonneg (atom0344_nonneg g hg hA hB) (atom0345_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0346_nonneg g hg hA hB) (add_nonneg (atom0347_nonneg g hg hA hB) (atom0348_nonneg g hg hA hB))) (add_nonneg (atom0349_nonneg g hg hA hB) (add_nonneg (atom0350_nonneg g hg hA hB) (atom0351_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0352_nonneg g hg hA hB) (atom0353_nonneg g hg hA hB)) (add_nonneg (atom0354_nonneg g hg hA hB) (add_nonneg (atom0355_nonneg g hg hA hB) (atom0356_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0357_nonneg g hg hA hB) (add_nonneg (atom0358_nonneg g hg hA hB) (atom0359_nonneg g hg hA hB))) (add_nonneg (atom0360_nonneg g hg hA hB) (add_nonneg (atom0361_nonneg g hg hA hB) (atom0362_nonneg g hg hA hB)))))))

end APPT.Finite12
