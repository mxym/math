import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0415 : SparsePolynomial.Poly := [([2,2,2], 1)]
theorem eval_atom0415 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0415 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0415, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0415_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (841881600 : Int) atom0415) := by
  rw [SparsePolynomial.eval_scale, eval_atom0415]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0416 : SparsePolynomial.Poly := [([2,2,3], 1)]
theorem eval_atom0416 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0416 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0416, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0416_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2365009920 : Int) atom0416) := by
  rw [SparsePolynomial.eval_scale, eval_atom0416]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0417 : SparsePolynomial.Poly := [([2,2,4], 1)]
theorem eval_atom0417 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0417 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0417, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0417_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2204375040 : Int) atom0417) := by
  rw [SparsePolynomial.eval_scale, eval_atom0417]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0418 : SparsePolynomial.Poly := [([2,2,5], 1)]
theorem eval_atom0418 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0418 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0418, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0418_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2043740160 : Int) atom0418) := by
  rw [SparsePolynomial.eval_scale, eval_atom0418]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0419 : SparsePolynomial.Poly := [([2,2,6], 1)]
theorem eval_atom0419 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0419 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0419, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0419_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1883105280 : Int) atom0419) := by
  rw [SparsePolynomial.eval_scale, eval_atom0419]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0420 : SparsePolynomial.Poly := [([2,2,7], 1)]
theorem eval_atom0420 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0420 = ((g 2) * (g 2) * (g 7)) := by
  norm_num [atom0420, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0420_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1722470400 : Int) atom0420) := by
  rw [SparsePolynomial.eval_scale, eval_atom0420]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0421 : SparsePolynomial.Poly := [([2,2,8], 1)]
theorem eval_atom0421 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0421 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0421, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0421_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1613068800 : Int) atom0421) := by
  rw [SparsePolynomial.eval_scale, eval_atom0421]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0422 : SparsePolynomial.Poly := [([2,2,9], 1)]
theorem eval_atom0422 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0422 = ((g 2) * (g 2) * (g 9)) := by
  norm_num [atom0422, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0422_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1443402240 : Int) atom0422) := by
  rw [SparsePolynomial.eval_scale, eval_atom0422]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0423 : SparsePolynomial.Poly := [([2,2,10], 1)]
theorem eval_atom0423 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0423 = ((g 2) * (g 2) * (g 10)) := by
  norm_num [atom0423, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0423_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1298895360 : Int) atom0423) := by
  rw [SparsePolynomial.eval_scale, eval_atom0423]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0424 : SparsePolynomial.Poly := [([2,2,11], 1)]
theorem eval_atom0424 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0424 = ((g 2) * (g 2) * (g 11)) := by
  norm_num [atom0424, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0424_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1079930880 : Int) atom0424) := by
  rw [SparsePolynomial.eval_scale, eval_atom0424]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0425 : SparsePolynomial.Poly := [([2,2,12], 1)]
theorem eval_atom0425 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0425 = ((g 2) * (g 2) * (g 12)) := by
  norm_num [atom0425, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0425_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2695956480 : Int) atom0425) := by
  rw [SparsePolynomial.eval_scale, eval_atom0425]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0426 : SparsePolynomial.Poly := [([2,2,13], 1)]
theorem eval_atom0426 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0426 = ((g 2) * (g 2) * (g 13)) := by
  norm_num [atom0426, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0426_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (758661120 : Int) atom0426) := by
  rw [SparsePolynomial.eval_scale, eval_atom0426]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0427 : SparsePolynomial.Poly := [([2,2,14], 1)]
theorem eval_atom0427 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0427 = ((g 2) * (g 2) * (g 14)) := by
  norm_num [atom0427, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0427_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2267079120 : Int) atom0427) := by
  rw [SparsePolynomial.eval_scale, eval_atom0427]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0428 : SparsePolynomial.Poly := [([2,2,15], 1)]
theorem eval_atom0428 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0428 = ((g 2) * (g 2) * (g 15)) := by
  norm_num [atom0428, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0428_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (437391360 : Int) atom0428) := by
  rw [SparsePolynomial.eval_scale, eval_atom0428]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0429 : SparsePolynomial.Poly := [([2,2,17], 1)]
theorem eval_atom0429 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0429 = ((g 2) * (g 2) * (g 17)) := by
  norm_num [atom0429, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0429_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (737049600 : Int) atom0429) := by
  rw [SparsePolynomial.eval_scale, eval_atom0429]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0430 : SparsePolynomial.Poly := [([2,3,3], 1)]
theorem eval_atom0430 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0430 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0430, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0430_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1892782080 : Int) atom0430) := by
  rw [SparsePolynomial.eval_scale, eval_atom0430]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0431 : SparsePolynomial.Poly := [([2,3,4], 1)]
theorem eval_atom0431 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0431 = ((g 2) * (g 3) * (g 4)) := by
  norm_num [atom0431, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0431_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3615252480 : Int) atom0431) := by
  rw [SparsePolynomial.eval_scale, eval_atom0431]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0432 : SparsePolynomial.Poly := [([2,3,5], 1)]
theorem eval_atom0432 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0432 = ((g 2) * (g 3) * (g 5)) := by
  norm_num [atom0432, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0432_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3444940800 : Int) atom0432) := by
  rw [SparsePolynomial.eval_scale, eval_atom0432]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0433 : SparsePolynomial.Poly := [([2,3,6], 1)]
theorem eval_atom0433 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0433 = ((g 2) * (g 3) * (g 6)) := by
  norm_num [atom0433, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0433_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3274629120 : Int) atom0433) := by
  rw [SparsePolynomial.eval_scale, eval_atom0433]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0434 : SparsePolynomial.Poly := [([2,3,7], 1)]
theorem eval_atom0434 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0434 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0434, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0434_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3104317440 : Int) atom0434) := by
  rw [SparsePolynomial.eval_scale, eval_atom0434]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0435 : SparsePolynomial.Poly := [([2,3,8], 1)]
theorem eval_atom0435 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0435 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0435, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0435_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3036472320 : Int) atom0435) := by
  rw [SparsePolynomial.eval_scale, eval_atom0435]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0436 : SparsePolynomial.Poly := [([2,3,9], 1)]
theorem eval_atom0436 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0436 = ((g 2) * (g 3) * (g 9)) := by
  norm_num [atom0436, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0436_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2848097280 : Int) atom0436) := by
  rw [SparsePolynomial.eval_scale, eval_atom0436]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0437 : SparsePolynomial.Poly := [([2,3,10], 1)]
theorem eval_atom0437 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0437 = ((g 2) * (g 3) * (g 10)) := by
  norm_num [atom0437, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0437_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2710041600 : Int) atom0437) := by
  rw [SparsePolynomial.eval_scale, eval_atom0437]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0438 : SparsePolynomial.Poly := [([2,3,11], 1)]
theorem eval_atom0438 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0438 = ((g 2) * (g 3) * (g 11)) := by
  norm_num [atom0438, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0438_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2584350720 : Int) atom0438) := by
  rw [SparsePolynomial.eval_scale, eval_atom0438]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0439 : SparsePolynomial.Poly := [([2,3,12], 1)]
theorem eval_atom0439 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0439 = ((g 2) * (g 3) * (g 12)) := by
  norm_num [atom0439, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0439_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5806080000 : Int) atom0439) := by
  rw [SparsePolynomial.eval_scale, eval_atom0439]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0440 : SparsePolynomial.Poly := [([2,3,13], 1)]
theorem eval_atom0440 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0440 = ((g 2) * (g 3) * (g 13)) := by
  norm_num [atom0440, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0440_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2470809600 : Int) atom0440) := by
  rw [SparsePolynomial.eval_scale, eval_atom0440]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0441 : SparsePolynomial.Poly := [([2,3,14], 1)]
theorem eval_atom0441 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0441 = ((g 2) * (g 3) * (g 14)) := by
  norm_num [atom0441, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0441_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5250241440 : Int) atom0441) := by
  rw [SparsePolynomial.eval_scale, eval_atom0441]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0442 : SparsePolynomial.Poly := [([2,3,15], 1)]
theorem eval_atom0442 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0442 = ((g 2) * (g 3) * (g 15)) := by
  norm_num [atom0442, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0442_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2357268480 : Int) atom0442) := by
  rw [SparsePolynomial.eval_scale, eval_atom0442]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0443 : SparsePolynomial.Poly := [([2,3,16], 1)]
theorem eval_atom0443 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0443 = ((g 2) * (g 3) * (g 16)) := by
  norm_num [atom0443, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0443_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2023741440 : Int) atom0443) := by
  rw [SparsePolynomial.eval_scale, eval_atom0443]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0444 : SparsePolynomial.Poly := [([2,3,17], 1)]
theorem eval_atom0444 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0444 = ((g 2) * (g 3) * (g 17)) := by
  norm_num [atom0444, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0444_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2864655360 : Int) atom0444) := by
  rw [SparsePolynomial.eval_scale, eval_atom0444]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0445 : SparsePolynomial.Poly := [([2,4,4], 1)]
theorem eval_atom0445 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0445 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0445, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0445_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2651174400 : Int) atom0445) := by
  rw [SparsePolynomial.eval_scale, eval_atom0445]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0446 : SparsePolynomial.Poly := [([2,4,5], 1)]
theorem eval_atom0446 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0446 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0446, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0446_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4383626880 : Int) atom0446) := by
  rw [SparsePolynomial.eval_scale, eval_atom0446]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0447 : SparsePolynomial.Poly := [([2,4,6], 1)]
theorem eval_atom0447 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0447 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0447, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0447_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3392077440 : Int) atom0447) := by
  rw [SparsePolynomial.eval_scale, eval_atom0447]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0448 : SparsePolynomial.Poly := [([2,4,7], 1)]
theorem eval_atom0448 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0448 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0448, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0448_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2877504000 : Int) atom0448) := by
  rw [SparsePolynomial.eval_scale, eval_atom0448]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0449 : SparsePolynomial.Poly := [([2,4,8], 1)]
theorem eval_atom0449 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0449 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0449, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0449_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2846807040 : Int) atom0449) := by
  rw [SparsePolynomial.eval_scale, eval_atom0449]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0450 : SparsePolynomial.Poly := [([2,4,9], 1)]
theorem eval_atom0450 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0450 = ((g 2) * (g 4) * (g 9)) := by
  norm_num [atom0450, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0450_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2809390080 : Int) atom0450) := by
  rw [SparsePolynomial.eval_scale, eval_atom0450]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0451 : SparsePolynomial.Poly := [([2,4,10], 1)]
theorem eval_atom0451 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0451 = ((g 2) * (g 4) * (g 10)) := by
  norm_num [atom0451, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0451_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2822292480 : Int) atom0451) := by
  rw [SparsePolynomial.eval_scale, eval_atom0451]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0452 : SparsePolynomial.Poly := [([2,4,11], 1)]
theorem eval_atom0452 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0452 = ((g 2) * (g 4) * (g 11)) := by
  norm_num [atom0452, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0452_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2760737280 : Int) atom0452) := by
  rw [SparsePolynomial.eval_scale, eval_atom0452]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0453 : SparsePolynomial.Poly := [([2,4,12], 1)]
theorem eval_atom0453 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0453 = ((g 2) * (g 4) * (g 12)) := by
  norm_num [atom0453, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0453_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6220247040 : Int) atom0453) := by
  rw [SparsePolynomial.eval_scale, eval_atom0453]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0454 : SparsePolynomial.Poly := [([2,4,13], 1)]
theorem eval_atom0454 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0454 = ((g 2) * (g 4) * (g 13)) := by
  norm_num [atom0454, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0454_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3219397440 : Int) atom0454) := by
  rw [SparsePolynomial.eval_scale, eval_atom0454]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0455 : SparsePolynomial.Poly := [([2,4,14], 1)]
theorem eval_atom0455 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0455 = ((g 2) * (g 4) * (g 14)) := by
  norm_num [atom0455, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0455_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5966324640 : Int) atom0455) := by
  rw [SparsePolynomial.eval_scale, eval_atom0455]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0456 : SparsePolynomial.Poly := [([2,4,15], 1)]
theorem eval_atom0456 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0456 = ((g 2) * (g 4) * (g 15)) := by
  norm_num [atom0456, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0456_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4143168960 : Int) atom0456) := by
  rw [SparsePolynomial.eval_scale, eval_atom0456]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0457 : SparsePolynomial.Poly := [([2,4,16], 1)]
theorem eval_atom0457 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0457 = ((g 2) * (g 4) * (g 16)) := by
  norm_num [atom0457, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0457_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4483335360 : Int) atom0457) := by
  rw [SparsePolynomial.eval_scale, eval_atom0457]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0458 : SparsePolynomial.Poly := [([2,4,17], 1)]
theorem eval_atom0458 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0458 = ((g 2) * (g 4) * (g 17)) := by
  norm_num [atom0458, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0458_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5997942720 : Int) atom0458) := by
  rw [SparsePolynomial.eval_scale, eval_atom0458]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0459 : SparsePolynomial.Poly := [([2,5,5], 1)]
theorem eval_atom0459 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0459 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0459, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0459_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2717550720 : Int) atom0459) := by
  rw [SparsePolynomial.eval_scale, eval_atom0459]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0460 : SparsePolynomial.Poly := [([2,5,6], 1)]
theorem eval_atom0460 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0460 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0460, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0460_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4500322560 : Int) atom0460) := by
  rw [SparsePolynomial.eval_scale, eval_atom0460]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0461 : SparsePolynomial.Poly := [([2,5,7], 1)]
theorem eval_atom0461 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0461 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0461, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0461_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3796225920 : Int) atom0461) := by
  rw [SparsePolynomial.eval_scale, eval_atom0461]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0462 : SparsePolynomial.Poly := [([2,5,8], 1)]
theorem eval_atom0462 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0462 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0462, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0462_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3822299520 : Int) atom0462) := by
  rw [SparsePolynomial.eval_scale, eval_atom0462]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0463 : SparsePolynomial.Poly := [([2,5,9], 1)]
theorem eval_atom0463 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0463 = ((g 2) * (g 5) * (g 9)) := by
  norm_num [atom0463, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0463_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3734563200 : Int) atom0463) := by
  rw [SparsePolynomial.eval_scale, eval_atom0463]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0464 : SparsePolynomial.Poly := [([2,5,10], 1)]
theorem eval_atom0464 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0464 = ((g 2) * (g 5) * (g 10)) := by
  norm_num [atom0464, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0464_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3750691200 : Int) atom0464) := by
  rw [SparsePolynomial.eval_scale, eval_atom0464]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0465 : SparsePolynomial.Poly := [([2,5,11], 1)]
theorem eval_atom0465 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0465 = ((g 2) * (g 5) * (g 11)) := by
  norm_num [atom0465, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0465_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3692361600 : Int) atom0465) := by
  rw [SparsePolynomial.eval_scale, eval_atom0465]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0466 : SparsePolynomial.Poly := [([2,5,12], 1)]
theorem eval_atom0466 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0466 = ((g 2) * (g 5) * (g 12)) := by
  norm_num [atom0466, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0466_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6634414080 : Int) atom0466) := by
  rw [SparsePolynomial.eval_scale, eval_atom0466]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0467 : SparsePolynomial.Poly := [([2,5,13], 1)]
theorem eval_atom0467 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0467 = ((g 2) * (g 5) * (g 13)) := by
  norm_num [atom0467, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0467_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4306469040 : Int) atom0467) := by
  rw [SparsePolynomial.eval_scale, eval_atom0467]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0468 : SparsePolynomial.Poly := [([2,5,14], 1)]
theorem eval_atom0468 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0468 = ((g 2) * (g 5) * (g 14)) := by
  norm_num [atom0468, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0468_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6682407840 : Int) atom0468) := by
  rw [SparsePolynomial.eval_scale, eval_atom0468]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0469 : SparsePolynomial.Poly := [([2,5,15], 1)]
theorem eval_atom0469 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0469 = ((g 2) * (g 5) * (g 15)) := by
  norm_num [atom0469, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0469_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5534683920 : Int) atom0469) := by
  rw [SparsePolynomial.eval_scale, eval_atom0469]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0470 : SparsePolynomial.Poly := [([2,5,16], 1)]
theorem eval_atom0470 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0470 = ((g 2) * (g 5) * (g 16)) := by
  norm_num [atom0470, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0470_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6076737360 : Int) atom0470) := by
  rw [SparsePolynomial.eval_scale, eval_atom0470]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0471 : SparsePolynomial.Poly := [([2,5,17], 1)]
theorem eval_atom0471 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0471 = ((g 2) * (g 5) * (g 17)) := by
  norm_num [atom0471, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0471_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7793231760 : Int) atom0471) := by
  rw [SparsePolynomial.eval_scale, eval_atom0471]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0472 : SparsePolynomial.Poly := [([2,6,6], 1)]
theorem eval_atom0472 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0472 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0472, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0472_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2767870080 : Int) atom0472) := by
  rw [SparsePolynomial.eval_scale, eval_atom0472]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0473 : SparsePolynomial.Poly := [([2,6,7], 1)]
theorem eval_atom0473 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0473 = ((g 2) * (g 6) * (g 7)) := by
  norm_num [atom0473, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0473_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4995504000 : Int) atom0473) := by
  rw [SparsePolynomial.eval_scale, eval_atom0473]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0474 : SparsePolynomial.Poly := [([2,6,8], 1)]
theorem eval_atom0474 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0474 = ((g 2) * (g 6) * (g 8)) := by
  norm_num [atom0474, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0474_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4920938880 : Int) atom0474) := by
  rw [SparsePolynomial.eval_scale, eval_atom0474]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0475 : SparsePolynomial.Poly := [([2,6,9], 1)]
theorem eval_atom0475 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0475 = ((g 2) * (g 6) * (g 9)) := by
  norm_num [atom0475, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0475_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4839653760 : Int) atom0475) := by
  rw [SparsePolynomial.eval_scale, eval_atom0475]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0476 : SparsePolynomial.Poly := [([2,6,10], 1)]
theorem eval_atom0476 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0476 = ((g 2) * (g 6) * (g 10)) := by
  norm_num [atom0476, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0476_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4808688000 : Int) atom0476) := by
  rw [SparsePolynomial.eval_scale, eval_atom0476]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0477 : SparsePolynomial.Poly := [([2,6,11], 1)]
theorem eval_atom0477 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0477 = ((g 2) * (g 6) * (g 11)) := by
  norm_num [atom0477, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0477_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4703264640 : Int) atom0477) := by
  rw [SparsePolynomial.eval_scale, eval_atom0477]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0478 : SparsePolynomial.Poly := [([2,6,12], 1)]
theorem eval_atom0478 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0478 = ((g 2) * (g 6) * (g 12)) := by
  norm_num [atom0478, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0478_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7048581120 : Int) atom0478) := by
  rw [SparsePolynomial.eval_scale, eval_atom0478]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0479 : SparsePolynomial.Poly := [([2,6,13], 1)]
theorem eval_atom0479 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0479 = ((g 2) * (g 6) * (g 13)) := by
  norm_num [atom0479, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0479_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5309550000 : Int) atom0479) := by
  rw [SparsePolynomial.eval_scale, eval_atom0479]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0480 : SparsePolynomial.Poly := [([2,6,14], 1)]
theorem eval_atom0480 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0480 = ((g 2) * (g 6) * (g 14)) := by
  norm_num [atom0480, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0480_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7398491040 : Int) atom0480) := by
  rw [SparsePolynomial.eval_scale, eval_atom0480]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0481 : SparsePolynomial.Poly := [([2,6,15], 1)]
theorem eval_atom0481 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0481 = ((g 2) * (g 6) * (g 15)) := by
  norm_num [atom0481, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0481_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6616308240 : Int) atom0481) := by
  rw [SparsePolynomial.eval_scale, eval_atom0481]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0482 : SparsePolynomial.Poly := [([2,6,16], 1)]
theorem eval_atom0482 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0482 = ((g 2) * (g 6) * (g 16)) := by
  norm_num [atom0482, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0482_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7226421840 : Int) atom0482) := by
  rw [SparsePolynomial.eval_scale, eval_atom0482]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0483 : SparsePolynomial.Poly := [([2,6,17], 1)]
theorem eval_atom0483 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0483 = ((g 2) * (g 6) * (g 17)) := by
  norm_num [atom0483, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0483_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9010976400 : Int) atom0483) := by
  rw [SparsePolynomial.eval_scale, eval_atom0483]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0484 : SparsePolynomial.Poly := [([2,7,7], 1)]
theorem eval_atom0484 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0484 = ((g 2) * (g 7) * (g 7)) := by
  norm_num [atom0484, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0484_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3212732160 : Int) atom0484) := by
  rw [SparsePolynomial.eval_scale, eval_atom0484]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0485 : SparsePolynomial.Poly := [([2,7,8], 1)]
theorem eval_atom0485 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0485 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0485, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0485_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5946305280 : Int) atom0485) := by
  rw [SparsePolynomial.eval_scale, eval_atom0485]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0486 : SparsePolynomial.Poly := [([2,7,9], 1)]
theorem eval_atom0486 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0486 = ((g 2) * (g 7) * (g 9)) := by
  norm_num [atom0486, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0486_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5714062080 : Int) atom0486) := by
  rw [SparsePolynomial.eval_scale, eval_atom0486]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0487 : SparsePolynomial.Poly := [([2,7,10], 1)]
theorem eval_atom0487 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0487 = ((g 2) * (g 7) * (g 10)) := by
  norm_num [atom0487, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0487_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5585683200 : Int) atom0487) := by
  rw [SparsePolynomial.eval_scale, eval_atom0487]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0488 : SparsePolynomial.Poly := [([2,7,11], 1)]
theorem eval_atom0488 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0488 = ((g 2) * (g 7) * (g 11)) := by
  norm_num [atom0488, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0488_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5382846720 : Int) atom0488) := by
  rw [SparsePolynomial.eval_scale, eval_atom0488]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0489 : SparsePolynomial.Poly := [([2,7,12], 1)]
theorem eval_atom0489 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0489 = ((g 2) * (g 7) * (g 12)) := by
  norm_num [atom0489, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0489_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7462748160 : Int) atom0489) := by
  rw [SparsePolynomial.eval_scale, eval_atom0489]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0490 : SparsePolynomial.Poly := [([2,7,13], 1)]
theorem eval_atom0490 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0490 = ((g 2) * (g 7) * (g 13)) := by
  norm_num [atom0490, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0490_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5972015520 : Int) atom0490) := by
  rw [SparsePolynomial.eval_scale, eval_atom0490]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0491 : SparsePolynomial.Poly := [([2,7,14], 1)]
theorem eval_atom0491 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0491 = ((g 2) * (g 7) * (g 14)) := by
  norm_num [atom0491, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0491_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8114574240 : Int) atom0491) := by
  rw [SparsePolynomial.eval_scale, eval_atom0491]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0492 : SparsePolynomial.Poly := [([2,7,15], 1)]
theorem eval_atom0492 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0492 = ((g 2) * (g 7) * (g 15)) := by
  norm_num [atom0492, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0492_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7439366880 : Int) atom0492) := by
  rw [SparsePolynomial.eval_scale, eval_atom0492]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0493 : SparsePolynomial.Poly := [([2,7,16], 1)]
theorem eval_atom0493 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0493 = ((g 2) * (g 7) * (g 16)) := by
  norm_num [atom0493, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0493_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8189013600 : Int) atom0493) := by
  rw [SparsePolynomial.eval_scale, eval_atom0493]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0494 : SparsePolynomial.Poly := [([2,7,17], 1)]
theorem eval_atom0494 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom0494 = ((g 2) * (g 7) * (g 17)) := by
  norm_num [atom0494, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0494_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10113101280 : Int) atom0494) := by
  rw [SparsePolynomial.eval_scale, eval_atom0494]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block006 : SparsePolynomial.Poly := [([2,2,2], 841881600), ([2,2,3], 2365009920), ([2,2,4], 2204375040), ([2,2,5], 2043740160), ([2,2,6], 1883105280), ([2,2,7], 1722470400), ([2,2,8], 1613068800), ([2,2,9], 1443402240), ([2,2,10], 1298895360), ([2,2,11], 1079930880), ([2,2,12], 2695956480), ([2,2,13], 758661120), ([2,2,14], 2267079120), ([2,2,15], 437391360), ([2,2,17], 737049600), ([2,3,3], 1892782080), ([2,3,4], 3615252480), ([2,3,5], 3444940800), ([2,3,6], 3274629120), ([2,3,7], 3104317440), ([2,3,8], 3036472320), ([2,3,9], 2848097280), ([2,3,10], 2710041600), ([2,3,11], 2584350720), ([2,3,12], 5806080000), ([2,3,13], 2470809600), ([2,3,14], 5250241440), ([2,3,15], 2357268480), ([2,3,16], 2023741440), ([2,3,17], 2864655360), ([2,4,4], 2651174400), ([2,4,5], 4383626880), ([2,4,6], 3392077440), ([2,4,7], 2877504000), ([2,4,8], 2846807040), ([2,4,9], 2809390080), ([2,4,10], 2822292480), ([2,4,11], 2760737280), ([2,4,12], 6220247040), ([2,4,13], 3219397440), ([2,4,14], 5966324640), ([2,4,15], 4143168960), ([2,4,16], 4483335360), ([2,4,17], 5997942720), ([2,5,5], 2717550720), ([2,5,6], 4500322560), ([2,5,7], 3796225920), ([2,5,8], 3822299520), ([2,5,9], 3734563200), ([2,5,10], 3750691200), ([2,5,11], 3692361600), ([2,5,12], 6634414080), ([2,5,13], 4306469040), ([2,5,14], 6682407840), ([2,5,15], 5534683920), ([2,5,16], 6076737360), ([2,5,17], 7793231760), ([2,6,6], 2767870080), ([2,6,7], 4995504000), ([2,6,8], 4920938880), ([2,6,9], 4839653760), ([2,6,10], 4808688000), ([2,6,11], 4703264640), ([2,6,12], 7048581120), ([2,6,13], 5309550000), ([2,6,14], 7398491040), ([2,6,15], 6616308240), ([2,6,16], 7226421840), ([2,6,17], 9010976400), ([2,7,7], 3212732160), ([2,7,8], 5946305280), ([2,7,9], 5714062080), ([2,7,10], 5585683200), ([2,7,11], 5382846720), ([2,7,12], 7462748160), ([2,7,13], 5972015520), ([2,7,14], 8114574240), ([2,7,15], 7439366880), ([2,7,16], 8189013600), ([2,7,17], 10113101280)]
theorem block006_data : block006 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (841881600 : Int) atom0415) (SparsePolynomial.scale (2365009920 : Int) atom0416)) (SparsePolynomial.merge (SparsePolynomial.scale (2204375040 : Int) atom0417) (SparsePolynomial.merge (SparsePolynomial.scale (2043740160 : Int) atom0418) (SparsePolynomial.scale (1883105280 : Int) atom0419)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1722470400 : Int) atom0420) (SparsePolynomial.scale (1613068800 : Int) atom0421)) (SparsePolynomial.merge (SparsePolynomial.scale (1443402240 : Int) atom0422) (SparsePolynomial.merge (SparsePolynomial.scale (1298895360 : Int) atom0423) (SparsePolynomial.scale (1079930880 : Int) atom0424))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2695956480 : Int) atom0425) (SparsePolynomial.scale (758661120 : Int) atom0426)) (SparsePolynomial.merge (SparsePolynomial.scale (2267079120 : Int) atom0427) (SparsePolynomial.merge (SparsePolynomial.scale (437391360 : Int) atom0428) (SparsePolynomial.scale (737049600 : Int) atom0429)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1892782080 : Int) atom0430) (SparsePolynomial.scale (3615252480 : Int) atom0431)) (SparsePolynomial.merge (SparsePolynomial.scale (3444940800 : Int) atom0432) (SparsePolynomial.merge (SparsePolynomial.scale (3274629120 : Int) atom0433) (SparsePolynomial.scale (3104317440 : Int) atom0434)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3036472320 : Int) atom0435) (SparsePolynomial.scale (2848097280 : Int) atom0436)) (SparsePolynomial.merge (SparsePolynomial.scale (2710041600 : Int) atom0437) (SparsePolynomial.merge (SparsePolynomial.scale (2584350720 : Int) atom0438) (SparsePolynomial.scale (5806080000 : Int) atom0439)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2470809600 : Int) atom0440) (SparsePolynomial.scale (5250241440 : Int) atom0441)) (SparsePolynomial.merge (SparsePolynomial.scale (2357268480 : Int) atom0442) (SparsePolynomial.merge (SparsePolynomial.scale (2023741440 : Int) atom0443) (SparsePolynomial.scale (2864655360 : Int) atom0444))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2651174400 : Int) atom0445) (SparsePolynomial.scale (4383626880 : Int) atom0446)) (SparsePolynomial.merge (SparsePolynomial.scale (3392077440 : Int) atom0447) (SparsePolynomial.merge (SparsePolynomial.scale (2877504000 : Int) atom0448) (SparsePolynomial.scale (2846807040 : Int) atom0449)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2809390080 : Int) atom0450) (SparsePolynomial.scale (2822292480 : Int) atom0451)) (SparsePolynomial.merge (SparsePolynomial.scale (2760737280 : Int) atom0452) (SparsePolynomial.merge (SparsePolynomial.scale (6220247040 : Int) atom0453) (SparsePolynomial.scale (3219397440 : Int) atom0454))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5966324640 : Int) atom0455) (SparsePolynomial.scale (4143168960 : Int) atom0456)) (SparsePolynomial.merge (SparsePolynomial.scale (4483335360 : Int) atom0457) (SparsePolynomial.merge (SparsePolynomial.scale (5997942720 : Int) atom0458) (SparsePolynomial.scale (2717550720 : Int) atom0459)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4500322560 : Int) atom0460) (SparsePolynomial.scale (3796225920 : Int) atom0461)) (SparsePolynomial.merge (SparsePolynomial.scale (3822299520 : Int) atom0462) (SparsePolynomial.merge (SparsePolynomial.scale (3734563200 : Int) atom0463) (SparsePolynomial.scale (3750691200 : Int) atom0464))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3692361600 : Int) atom0465) (SparsePolynomial.scale (6634414080 : Int) atom0466)) (SparsePolynomial.merge (SparsePolynomial.scale (4306469040 : Int) atom0467) (SparsePolynomial.merge (SparsePolynomial.scale (6682407840 : Int) atom0468) (SparsePolynomial.scale (5534683920 : Int) atom0469)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6076737360 : Int) atom0470) (SparsePolynomial.scale (7793231760 : Int) atom0471)) (SparsePolynomial.merge (SparsePolynomial.scale (2767870080 : Int) atom0472) (SparsePolynomial.merge (SparsePolynomial.scale (4995504000 : Int) atom0473) (SparsePolynomial.scale (4920938880 : Int) atom0474)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4839653760 : Int) atom0475) (SparsePolynomial.scale (4808688000 : Int) atom0476)) (SparsePolynomial.merge (SparsePolynomial.scale (4703264640 : Int) atom0477) (SparsePolynomial.merge (SparsePolynomial.scale (7048581120 : Int) atom0478) (SparsePolynomial.scale (5309550000 : Int) atom0479)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7398491040 : Int) atom0480) (SparsePolynomial.scale (6616308240 : Int) atom0481)) (SparsePolynomial.merge (SparsePolynomial.scale (7226421840 : Int) atom0482) (SparsePolynomial.merge (SparsePolynomial.scale (9010976400 : Int) atom0483) (SparsePolynomial.scale (3212732160 : Int) atom0484))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5946305280 : Int) atom0485) (SparsePolynomial.scale (5714062080 : Int) atom0486)) (SparsePolynomial.merge (SparsePolynomial.scale (5585683200 : Int) atom0487) (SparsePolynomial.merge (SparsePolynomial.scale (5382846720 : Int) atom0488) (SparsePolynomial.scale (7462748160 : Int) atom0489)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5972015520 : Int) atom0490) (SparsePolynomial.scale (8114574240 : Int) atom0491)) (SparsePolynomial.merge (SparsePolynomial.scale (7439366880 : Int) atom0492) (SparsePolynomial.merge (SparsePolynomial.scale (8189013600 : Int) atom0493) (SparsePolynomial.scale (10113101280 : Int) atom0494)))))))) := by decide +kernel
theorem block006_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block006 := by
  rw [block006_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0415_nonneg g hg hA hB) (atom0416_nonneg g hg hA hB)) (add_nonneg (atom0417_nonneg g hg hA hB) (add_nonneg (atom0418_nonneg g hg hA hB) (atom0419_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0420_nonneg g hg hA hB) (atom0421_nonneg g hg hA hB)) (add_nonneg (atom0422_nonneg g hg hA hB) (add_nonneg (atom0423_nonneg g hg hA hB) (atom0424_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0425_nonneg g hg hA hB) (atom0426_nonneg g hg hA hB)) (add_nonneg (atom0427_nonneg g hg hA hB) (add_nonneg (atom0428_nonneg g hg hA hB) (atom0429_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0430_nonneg g hg hA hB) (atom0431_nonneg g hg hA hB)) (add_nonneg (atom0432_nonneg g hg hA hB) (add_nonneg (atom0433_nonneg g hg hA hB) (atom0434_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0435_nonneg g hg hA hB) (atom0436_nonneg g hg hA hB)) (add_nonneg (atom0437_nonneg g hg hA hB) (add_nonneg (atom0438_nonneg g hg hA hB) (atom0439_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0440_nonneg g hg hA hB) (atom0441_nonneg g hg hA hB)) (add_nonneg (atom0442_nonneg g hg hA hB) (add_nonneg (atom0443_nonneg g hg hA hB) (atom0444_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0445_nonneg g hg hA hB) (atom0446_nonneg g hg hA hB)) (add_nonneg (atom0447_nonneg g hg hA hB) (add_nonneg (atom0448_nonneg g hg hA hB) (atom0449_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0450_nonneg g hg hA hB) (atom0451_nonneg g hg hA hB)) (add_nonneg (atom0452_nonneg g hg hA hB) (add_nonneg (atom0453_nonneg g hg hA hB) (atom0454_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0455_nonneg g hg hA hB) (atom0456_nonneg g hg hA hB)) (add_nonneg (atom0457_nonneg g hg hA hB) (add_nonneg (atom0458_nonneg g hg hA hB) (atom0459_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0460_nonneg g hg hA hB) (atom0461_nonneg g hg hA hB)) (add_nonneg (atom0462_nonneg g hg hA hB) (add_nonneg (atom0463_nonneg g hg hA hB) (atom0464_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0465_nonneg g hg hA hB) (atom0466_nonneg g hg hA hB)) (add_nonneg (atom0467_nonneg g hg hA hB) (add_nonneg (atom0468_nonneg g hg hA hB) (atom0469_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0470_nonneg g hg hA hB) (atom0471_nonneg g hg hA hB)) (add_nonneg (atom0472_nonneg g hg hA hB) (add_nonneg (atom0473_nonneg g hg hA hB) (atom0474_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0475_nonneg g hg hA hB) (atom0476_nonneg g hg hA hB)) (add_nonneg (atom0477_nonneg g hg hA hB) (add_nonneg (atom0478_nonneg g hg hA hB) (atom0479_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0480_nonneg g hg hA hB) (atom0481_nonneg g hg hA hB)) (add_nonneg (atom0482_nonneg g hg hA hB) (add_nonneg (atom0483_nonneg g hg hA hB) (atom0484_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0485_nonneg g hg hA hB) (atom0486_nonneg g hg hA hB)) (add_nonneg (atom0487_nonneg g hg hA hB) (add_nonneg (atom0488_nonneg g hg hA hB) (atom0489_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0490_nonneg g hg hA hB) (atom0491_nonneg g hg hA hB)) (add_nonneg (atom0492_nonneg g hg hA hB) (add_nonneg (atom0493_nonneg g hg hA hB) (atom0494_nonneg g hg hA hB))))))))

end APPT.Finite18
