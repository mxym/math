import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0335 : SparsePolynomial.Poly := [([1,5,16], 1)]
theorem eval_atom0335 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0335 = ((g 1) * (g 5) * (g 16)) := by
  norm_num [atom0335, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0335_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5898088840 : Int) atom0335) := by
  rw [SparsePolynomial.eval_scale, eval_atom0335]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0336 : SparsePolynomial.Poly := [([1,5,17], 1)]
theorem eval_atom0336 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0336 = ((g 1) * (g 5) * (g 17)) := by
  norm_num [atom0336, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0336_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6018711240 : Int) atom0336) := by
  rw [SparsePolynomial.eval_scale, eval_atom0336]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0337 : SparsePolynomial.Poly := [([1,6,6], 1)]
theorem eval_atom0337 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0337 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0337, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0337_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2000907360 : Int) atom0337) := by
  rw [SparsePolynomial.eval_scale, eval_atom0337]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0338 : SparsePolynomial.Poly := [([1,6,7], 1)]
theorem eval_atom0338 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0338 = ((g 1) * (g 6) * (g 7)) := by
  norm_num [atom0338, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0338_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3212404128 : Int) atom0338) := by
  rw [SparsePolynomial.eval_scale, eval_atom0338]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0339 : SparsePolynomial.Poly := [([1,6,8], 1)]
theorem eval_atom0339 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0339 = ((g 1) * (g 6) * (g 8)) := by
  norm_num [atom0339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0339_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2905871040 : Int) atom0339) := by
  rw [SparsePolynomial.eval_scale, eval_atom0339]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0340 : SparsePolynomial.Poly := [([1,6,9], 1)]
theorem eval_atom0340 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0340 = ((g 1) * (g 6) * (g 9)) := by
  norm_num [atom0340, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0340_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2903290560 : Int) atom0340) := by
  rw [SparsePolynomial.eval_scale, eval_atom0340]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0341 : SparsePolynomial.Poly := [([1,6,10], 1)]
theorem eval_atom0341 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0341 = ((g 1) * (g 6) * (g 10)) := by
  norm_num [atom0341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0341_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2951029440 : Int) atom0341) := by
  rw [SparsePolynomial.eval_scale, eval_atom0341]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0342 : SparsePolynomial.Poly := [([1,6,11], 1)]
theorem eval_atom0342 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0342 = ((g 1) * (g 6) * (g 11)) := by
  norm_num [atom0342, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0342_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3174733760 : Int) atom0342) := by
  rw [SparsePolynomial.eval_scale, eval_atom0342]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0343 : SparsePolynomial.Poly := [([1,6,12], 1)]
theorem eval_atom0343 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0343 = ((g 1) * (g 6) * (g 12)) := by
  norm_num [atom0343, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0343_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5883494400 : Int) atom0343) := by
  rw [SparsePolynomial.eval_scale, eval_atom0343]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0344 : SparsePolynomial.Poly := [([1,6,13], 1)]
theorem eval_atom0344 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0344 = ((g 1) * (g 6) * (g 13)) := by
  norm_num [atom0344, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0344_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4456174040 : Int) atom0344) := by
  rw [SparsePolynomial.eval_scale, eval_atom0344]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0345 : SparsePolynomial.Poly := [([1,6,14], 1)]
theorem eval_atom0345 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0345 = ((g 1) * (g 6) * (g 14)) := by
  norm_num [atom0345, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0345_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6098833080 : Int) atom0345) := by
  rw [SparsePolynomial.eval_scale, eval_atom0345]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0346 : SparsePolynomial.Poly := [([1,6,15], 1)]
theorem eval_atom0346 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0346 = ((g 1) * (g 6) * (g 15)) := by
  norm_num [atom0346, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0346_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5959982600 : Int) atom0346) := by
  rw [SparsePolynomial.eval_scale, eval_atom0346]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0347 : SparsePolynomial.Poly := [([1,6,16], 1)]
theorem eval_atom0347 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0347 = ((g 1) * (g 6) * (g 16)) := by
  norm_num [atom0347, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0347_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6391196200 : Int) atom0347) := by
  rw [SparsePolynomial.eval_scale, eval_atom0347]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0348 : SparsePolynomial.Poly := [([1,6,17], 1)]
theorem eval_atom0348 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0348 = ((g 1) * (g 6) * (g 17)) := by
  norm_num [atom0348, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0348_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6822409800 : Int) atom0348) := by
  rw [SparsePolynomial.eval_scale, eval_atom0348]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0349 : SparsePolynomial.Poly := [([1,7,7], 1)]
theorem eval_atom0349 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0349 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0349_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2336973120 : Int) atom0349) := by
  rw [SparsePolynomial.eval_scale, eval_atom0349]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0350 : SparsePolynomial.Poly := [([1,7,8], 1)]
theorem eval_atom0350 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0350 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0350, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0350_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3943380288 : Int) atom0350) := by
  rw [SparsePolynomial.eval_scale, eval_atom0350]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0351 : SparsePolynomial.Poly := [([1,7,9], 1)]
theorem eval_atom0351 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0351 = ((g 1) * (g 7) * (g 9)) := by
  norm_num [atom0351, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0351_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3334043520 : Int) atom0351) := by
  rw [SparsePolynomial.eval_scale, eval_atom0351]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0352 : SparsePolynomial.Poly := [([1,7,10], 1)]
theorem eval_atom0352 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0352 = ((g 1) * (g 7) * (g 10)) := by
  norm_num [atom0352, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0352_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3358235520 : Int) atom0352) := by
  rw [SparsePolynomial.eval_scale, eval_atom0352]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0353 : SparsePolynomial.Poly := [([1,7,11], 1)]
theorem eval_atom0353 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0353 = ((g 1) * (g 7) * (g 11)) := by
  norm_num [atom0353, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0353_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3558392960 : Int) atom0353) := by
  rw [SparsePolynomial.eval_scale, eval_atom0353]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0354 : SparsePolynomial.Poly := [([1,7,12], 1)]
theorem eval_atom0354 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0354 = ((g 1) * (g 7) * (g 12)) := by
  norm_num [atom0354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0354_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6159605760 : Int) atom0354) := by
  rw [SparsePolynomial.eval_scale, eval_atom0354]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0355 : SparsePolynomial.Poly := [([1,7,13], 1)]
theorem eval_atom0355 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0355 = ((g 1) * (g 7) * (g 13)) := by
  norm_num [atom0355, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0355_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4881594320 : Int) atom0355) := by
  rw [SparsePolynomial.eval_scale, eval_atom0355]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0356 : SparsePolynomial.Poly := [([1,7,14], 1)]
theorem eval_atom0356 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0356 = ((g 1) * (g 7) * (g 14)) := by
  norm_num [atom0356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0356_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6576221880 : Int) atom0356) := by
  rw [SparsePolynomial.eval_scale, eval_atom0356]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0357 : SparsePolynomial.Poly := [([1,7,15], 1)]
theorem eval_atom0357 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0357 = ((g 1) * (g 7) * (g 15)) := by
  norm_num [atom0357, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0357_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6516018800 : Int) atom0357) := by
  rw [SparsePolynomial.eval_scale, eval_atom0357]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0358 : SparsePolynomial.Poly := [([1,7,16], 1)]
theorem eval_atom0358 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0358 = ((g 1) * (g 7) * (g 16)) := by
  norm_num [atom0358, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0358_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7042158640 : Int) atom0358) := by
  rw [SparsePolynomial.eval_scale, eval_atom0358]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0359 : SparsePolynomial.Poly := [([1,7,17], 1)]
theorem eval_atom0359 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0359 = ((g 1) * (g 7) * (g 17)) := by
  norm_num [atom0359, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0359_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7568298480 : Int) atom0359) := by
  rw [SparsePolynomial.eval_scale, eval_atom0359]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0360 : SparsePolynomial.Poly := [([1,8,8], 1)]
theorem eval_atom0360 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0360 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0360, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0360_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2731883520 : Int) atom0360) := by
  rw [SparsePolynomial.eval_scale, eval_atom0360]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0361 : SparsePolynomial.Poly := [([1,8,9], 1)]
theorem eval_atom0361 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0361 = ((g 1) * (g 8) * (g 9)) := by
  norm_num [atom0361, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0361_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4672629120 : Int) atom0361) := by
  rw [SparsePolynomial.eval_scale, eval_atom0361]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0362 : SparsePolynomial.Poly := [([1,8,10], 1)]
theorem eval_atom0362 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0362 = ((g 1) * (g 8) * (g 10)) := by
  norm_num [atom0362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0362_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3937045632 : Int) atom0362) := by
  rw [SparsePolynomial.eval_scale, eval_atom0362]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0363 : SparsePolynomial.Poly := [([1,8,11], 1)]
theorem eval_atom0363 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0363 = ((g 1) * (g 8) * (g 11)) := by
  norm_num [atom0363, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0363_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4045591040 : Int) atom0363) := by
  rw [SparsePolynomial.eval_scale, eval_atom0363]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0364 : SparsePolynomial.Poly := [([1,8,12], 1)]
theorem eval_atom0364 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0364 = ((g 1) * (g 8) * (g 12)) := by
  norm_num [atom0364, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0364_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6538183680 : Int) atom0364) := by
  rw [SparsePolynomial.eval_scale, eval_atom0364]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0365 : SparsePolynomial.Poly := [([1,8,13], 1)]
theorem eval_atom0365 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0365 = ((g 1) * (g 8) * (g 13)) := by
  norm_num [atom0365, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0365_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5324168960 : Int) atom0365) := by
  rw [SparsePolynomial.eval_scale, eval_atom0365]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0366 : SparsePolynomial.Poly := [([1,8,14], 1)]
theorem eval_atom0366 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0366 = ((g 1) * (g 8) * (g 14)) := by
  norm_num [atom0366, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0366_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7156077240 : Int) atom0366) := by
  rw [SparsePolynomial.eval_scale, eval_atom0366]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0367 : SparsePolynomial.Poly := [([1,8,15], 1)]
theorem eval_atom0367 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0367 = ((g 1) * (g 8) * (g 15)) := by
  norm_num [atom0367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0367_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6966759680 : Int) atom0367) := by
  rw [SparsePolynomial.eval_scale, eval_atom0367]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0368 : SparsePolynomial.Poly := [([1,8,16], 1)]
theorem eval_atom0368 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0368 = ((g 1) * (g 8) * (g 16)) := by
  norm_num [atom0368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0368_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7463345920 : Int) atom0368) := by
  rw [SparsePolynomial.eval_scale, eval_atom0368]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0369 : SparsePolynomial.Poly := [([1,8,17], 1)]
theorem eval_atom0369 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0369 = ((g 1) * (g 8) * (g 17)) := by
  norm_num [atom0369, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0369_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8011165440 : Int) atom0369) := by
  rw [SparsePolynomial.eval_scale, eval_atom0369]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0370 : SparsePolynomial.Poly := [([1,9,9], 1)]
theorem eval_atom0370 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0370 = ((g 1) * (g 9) * (g 9)) := by
  norm_num [atom0370, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0370_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3038632320 : Int) atom0370) := by
  rw [SparsePolynomial.eval_scale, eval_atom0370]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0371 : SparsePolynomial.Poly := [([1,9,10], 1)]
theorem eval_atom0371 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0371 = ((g 1) * (g 9) * (g 10)) := by
  norm_num [atom0371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0371_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5210772480 : Int) atom0371) := by
  rw [SparsePolynomial.eval_scale, eval_atom0371]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0372 : SparsePolynomial.Poly := [([1,9,11], 1)]
theorem eval_atom0372 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0372 = ((g 1) * (g 9) * (g 11)) := by
  norm_num [atom0372, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0372_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4660776320 : Int) atom0372) := by
  rw [SparsePolynomial.eval_scale, eval_atom0372]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0373 : SparsePolynomial.Poly := [([1,9,12], 1)]
theorem eval_atom0373 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0373 = ((g 1) * (g 9) * (g 12)) := by
  norm_num [atom0373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0373_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6904803360 : Int) atom0373) := by
  rw [SparsePolynomial.eval_scale, eval_atom0373]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0374 : SparsePolynomial.Poly := [([1,9,13], 1)]
theorem eval_atom0374 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0374 = ((g 1) * (g 9) * (g 13)) := by
  norm_num [atom0374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0374_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5640737120 : Int) atom0374) := by
  rw [SparsePolynomial.eval_scale, eval_atom0374]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0375 : SparsePolynomial.Poly := [([1,9,14], 1)]
theorem eval_atom0375 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0375 = ((g 1) * (g 9) * (g 14)) := by
  norm_num [atom0375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0375_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7615402680 : Int) atom0375) := by
  rw [SparsePolynomial.eval_scale, eval_atom0375]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0376 : SparsePolynomial.Poly := [([1,9,15], 1)]
theorem eval_atom0376 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0376 = ((g 1) * (g 9) * (g 15)) := by
  norm_num [atom0376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0376_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7207039520 : Int) atom0376) := by
  rw [SparsePolynomial.eval_scale, eval_atom0376]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0377 : SparsePolynomial.Poly := [([1,9,16], 1)]
theorem eval_atom0377 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0377 = ((g 1) * (g 9) * (g 16)) := by
  norm_num [atom0377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0377_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7686420640 : Int) atom0377) := by
  rw [SparsePolynomial.eval_scale, eval_atom0377]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0378 : SparsePolynomial.Poly := [([1,9,17], 1)]
theorem eval_atom0378 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0378 = ((g 1) * (g 9) * (g 17)) := by
  norm_num [atom0378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0378_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8208003360 : Int) atom0378) := by
  rw [SparsePolynomial.eval_scale, eval_atom0378]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0379 : SparsePolynomial.Poly := [([1,10,10], 1)]
theorem eval_atom0379 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0379 = ((g 1) * (g 10) * (g 10)) := by
  norm_num [atom0379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0379_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3287337600 : Int) atom0379) := by
  rw [SparsePolynomial.eval_scale, eval_atom0379]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0380 : SparsePolynomial.Poly := [([1,10,11], 1)]
theorem eval_atom0380 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0380 = ((g 1) * (g 10) * (g 11)) := by
  norm_num [atom0380, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0380_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5911061120 : Int) atom0380) := by
  rw [SparsePolynomial.eval_scale, eval_atom0380]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0381 : SparsePolynomial.Poly := [([1,10,12], 1)]
theorem eval_atom0381 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0381 = ((g 1) * (g 10) * (g 12)) := by
  norm_num [atom0381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0381_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7349472480 : Int) atom0381) := by
  rw [SparsePolynomial.eval_scale, eval_atom0381]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0382 : SparsePolynomial.Poly := [([1,10,13], 1)]
theorem eval_atom0382 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0382 = ((g 1) * (g 10) * (g 13)) := by
  norm_num [atom0382, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0382_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5975361440 : Int) atom0382) := by
  rw [SparsePolynomial.eval_scale, eval_atom0382]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0383 : SparsePolynomial.Poly := [([1,10,14], 1)]
theorem eval_atom0383 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0383 = ((g 1) * (g 10) * (g 14)) := by
  norm_num [atom0383, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0383_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8125047480 : Int) atom0383) := by
  rw [SparsePolynomial.eval_scale, eval_atom0383]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0384 : SparsePolynomial.Poly := [([1,10,15], 1)]
theorem eval_atom0384 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0384 = ((g 1) * (g 10) * (g 15)) := by
  norm_num [atom0384, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0384_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7310555360 : Int) atom0384) := by
  rw [SparsePolynomial.eval_scale, eval_atom0384]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0385 : SparsePolynomial.Poly := [([1,10,16], 1)]
theorem eval_atom0385 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0385 = ((g 1) * (g 10) * (g 16)) := by
  norm_num [atom0385, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0385_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7652744800 : Int) atom0385) := by
  rw [SparsePolynomial.eval_scale, eval_atom0385]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0386 : SparsePolynomial.Poly := [([1,10,17], 1)]
theorem eval_atom0386 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0386 = ((g 1) * (g 10) * (g 17)) := by
  norm_num [atom0386, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0386_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8198641920 : Int) atom0386) := by
  rw [SparsePolynomial.eval_scale, eval_atom0386]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0387 : SparsePolynomial.Poly := [([1,11,11], 1)]
theorem eval_atom0387 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0387 = ((g 1) * (g 11) * (g 11)) := by
  norm_num [atom0387, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0387_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3794524160 : Int) atom0387) := by
  rw [SparsePolynomial.eval_scale, eval_atom0387]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0388 : SparsePolynomial.Poly := [([1,11,12], 1)]
theorem eval_atom0388 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0388 = ((g 1) * (g 11) * (g 12)) := by
  norm_num [atom0388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0388_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7850429440 : Int) atom0388) := by
  rw [SparsePolynomial.eval_scale, eval_atom0388]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0389 : SparsePolynomial.Poly := [([1,11,13], 1)]
theorem eval_atom0389 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0389 = ((g 1) * (g 11) * (g 13)) := by
  norm_num [atom0389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0389_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6205292800 : Int) atom0389) := by
  rw [SparsePolynomial.eval_scale, eval_atom0389]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0390 : SparsePolynomial.Poly := [([1,11,14], 1)]
theorem eval_atom0390 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0390 = ((g 1) * (g 11) * (g 14)) := by
  norm_num [atom0390, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0390_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8413864120 : Int) atom0390) := by
  rw [SparsePolynomial.eval_scale, eval_atom0390]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0391 : SparsePolynomial.Poly := [([1,11,15], 1)]
theorem eval_atom0391 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0391 = ((g 1) * (g 11) * (g 15)) := by
  norm_num [atom0391, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0391_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7605570560 : Int) atom0391) := by
  rw [SparsePolynomial.eval_scale, eval_atom0391]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0392 : SparsePolynomial.Poly := [([1,11,16], 1)]
theorem eval_atom0392 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0392 = ((g 1) * (g 11) * (g 16)) := by
  norm_num [atom0392, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0392_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7277580800 : Int) atom0392) := by
  rw [SparsePolynomial.eval_scale, eval_atom0392]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0393 : SparsePolynomial.Poly := [([1,11,17], 1)]
theorem eval_atom0393 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0393 = ((g 1) * (g 11) * (g 17)) := by
  norm_num [atom0393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0393_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8654338560 : Int) atom0393) := by
  rw [SparsePolynomial.eval_scale, eval_atom0393]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0394 : SparsePolynomial.Poly := [([1,12,12], 1)]
theorem eval_atom0394 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0394 = ((g 1) * (g 12) * (g 12)) := by
  norm_num [atom0394, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0394_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5546741760 : Int) atom0394) := by
  rw [SparsePolynomial.eval_scale, eval_atom0394]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0395 : SparsePolynomial.Poly := [([1,12,13], 1)]
theorem eval_atom0395 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0395 = ((g 1) * (g 12) * (g 13)) := by
  norm_num [atom0395, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0395_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8918250880 : Int) atom0395) := by
  rw [SparsePolynomial.eval_scale, eval_atom0395]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0396 : SparsePolynomial.Poly := [([1,12,14], 1)]
theorem eval_atom0396 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0396 = ((g 1) * (g 12) * (g 14)) := by
  norm_num [atom0396, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0396_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12516486840 : Int) atom0396) := by
  rw [SparsePolynomial.eval_scale, eval_atom0396]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0397 : SparsePolynomial.Poly := [([1,12,15], 1)]
theorem eval_atom0397 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0397 = ((g 1) * (g 12) * (g 15)) := by
  norm_num [atom0397, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0397_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11769116800 : Int) atom0397) := by
  rw [SparsePolynomial.eval_scale, eval_atom0397]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0398 : SparsePolynomial.Poly := [([1,12,16], 1)]
theorem eval_atom0398 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0398 = ((g 1) * (g 12) * (g 16)) := by
  norm_num [atom0398, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0398_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7645850240 : Int) atom0398) := by
  rw [SparsePolynomial.eval_scale, eval_atom0398]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0399 : SparsePolynomial.Poly := [([1,12,17], 1)]
theorem eval_atom0399 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0399 = ((g 1) * (g 12) * (g 17)) := by
  norm_num [atom0399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0399_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8873682720 : Int) atom0399) := by
  rw [SparsePolynomial.eval_scale, eval_atom0399]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0400 : SparsePolynomial.Poly := [([1,13,13], 1)]
theorem eval_atom0400 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0400 = ((g 1) * (g 13) * (g 13)) := by
  norm_num [atom0400, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0400_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3470027456 : Int) atom0400) := by
  rw [SparsePolynomial.eval_scale, eval_atom0400]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0401 : SparsePolynomial.Poly := [([1,13,14], 1)]
theorem eval_atom0401 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0401 = ((g 1) * (g 13) * (g 14)) := by
  norm_num [atom0401, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0401_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9201418000 : Int) atom0401) := by
  rw [SparsePolynomial.eval_scale, eval_atom0401]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0402 : SparsePolynomial.Poly := [([1,13,15], 1)]
theorem eval_atom0402 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0402 = ((g 1) * (g 13) * (g 15)) := by
  norm_num [atom0402, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0402_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10093237280 : Int) atom0402) := by
  rw [SparsePolynomial.eval_scale, eval_atom0402]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0403 : SparsePolynomial.Poly := [([1,13,16], 1)]
theorem eval_atom0403 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0403 = ((g 1) * (g 13) * (g 16)) := by
  norm_num [atom0403, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0403_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7347075680 : Int) atom0403) := by
  rw [SparsePolynomial.eval_scale, eval_atom0403]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0404 : SparsePolynomial.Poly := [([1,13,17], 1)]
theorem eval_atom0404 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0404 = ((g 1) * (g 13) * (g 17)) := by
  norm_num [atom0404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0404_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7882412160 : Int) atom0404) := by
  rw [SparsePolynomial.eval_scale, eval_atom0404]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0405 : SparsePolynomial.Poly := [([1,14,14], 1)]
theorem eval_atom0405 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0405 = ((g 1) * (g 14) * (g 14)) := by
  norm_num [atom0405, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0405_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6708730320 : Int) atom0405) := by
  rw [SparsePolynomial.eval_scale, eval_atom0405]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0406 : SparsePolynomial.Poly := [([1,14,15], 1)]
theorem eval_atom0406 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0406 = ((g 1) * (g 14) * (g 15)) := by
  norm_num [atom0406, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0406_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10927396240 : Int) atom0406) := by
  rw [SparsePolynomial.eval_scale, eval_atom0406]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0407 : SparsePolynomial.Poly := [([1,14,16], 1)]
theorem eval_atom0407 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0407 = ((g 1) * (g 14) * (g 16)) := by
  norm_num [atom0407, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0407_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8160306320 : Int) atom0407) := by
  rw [SparsePolynomial.eval_scale, eval_atom0407]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0408 : SparsePolynomial.Poly := [([1,14,17], 1)]
theorem eval_atom0408 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0408 = ((g 1) * (g 14) * (g 17)) := by
  norm_num [atom0408, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0408_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8967654960 : Int) atom0408) := by
  rw [SparsePolynomial.eval_scale, eval_atom0408]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0409 : SparsePolynomial.Poly := [([1,15,15], 1)]
theorem eval_atom0409 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0409 = ((g 1) * (g 15) * (g 15)) := by
  norm_num [atom0409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0409_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3992019360 : Int) atom0409) := by
  rw [SparsePolynomial.eval_scale, eval_atom0409]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0410 : SparsePolynomial.Poly := [([1,15,16], 1)]
theorem eval_atom0410 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0410 = ((g 1) * (g 15) * (g 16)) := by
  norm_num [atom0410, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0410_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5176124800 : Int) atom0410) := by
  rw [SparsePolynomial.eval_scale, eval_atom0410]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0411 : SparsePolynomial.Poly := [([1,15,17], 1)]
theorem eval_atom0411 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0411 = ((g 1) * (g 15) * (g 17)) := by
  norm_num [atom0411, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0411_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5897774400 : Int) atom0411) := by
  rw [SparsePolynomial.eval_scale, eval_atom0411]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0412 : SparsePolynomial.Poly := [([1,16,16], 1)]
theorem eval_atom0412 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0412 = ((g 1) * (g 16) * (g 16)) := by
  norm_num [atom0412, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0412_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (769123040 : Int) atom0412) := by
  rw [SparsePolynomial.eval_scale, eval_atom0412]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0413 : SparsePolynomial.Poly := [([1,16,17], 1)]
theorem eval_atom0413 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0413 = ((g 1) * (g 16) * (g 17)) := by
  norm_num [atom0413, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0413_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1724694720 : Int) atom0413) := by
  rw [SparsePolynomial.eval_scale, eval_atom0413]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0414 : SparsePolynomial.Poly := [([1,17,17], 1)]
theorem eval_atom0414 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0414 = ((g 1) * (g 17) * (g 17)) := by
  norm_num [atom0414, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0414_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (333335520 : Int) atom0414) := by
  rw [SparsePolynomial.eval_scale, eval_atom0414]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block005 : SparsePolynomial.Poly := [([1,5,16], 5898088840), ([1,5,17], 6018711240), ([1,6,6], 2000907360), ([1,6,7], 3212404128), ([1,6,8], 2905871040), ([1,6,9], 2903290560), ([1,6,10], 2951029440), ([1,6,11], 3174733760), ([1,6,12], 5883494400), ([1,6,13], 4456174040), ([1,6,14], 6098833080), ([1,6,15], 5959982600), ([1,6,16], 6391196200), ([1,6,17], 6822409800), ([1,7,7], 2336973120), ([1,7,8], 3943380288), ([1,7,9], 3334043520), ([1,7,10], 3358235520), ([1,7,11], 3558392960), ([1,7,12], 6159605760), ([1,7,13], 4881594320), ([1,7,14], 6576221880), ([1,7,15], 6516018800), ([1,7,16], 7042158640), ([1,7,17], 7568298480), ([1,8,8], 2731883520), ([1,8,9], 4672629120), ([1,8,10], 3937045632), ([1,8,11], 4045591040), ([1,8,12], 6538183680), ([1,8,13], 5324168960), ([1,8,14], 7156077240), ([1,8,15], 6966759680), ([1,8,16], 7463345920), ([1,8,17], 8011165440), ([1,9,9], 3038632320), ([1,9,10], 5210772480), ([1,9,11], 4660776320), ([1,9,12], 6904803360), ([1,9,13], 5640737120), ([1,9,14], 7615402680), ([1,9,15], 7207039520), ([1,9,16], 7686420640), ([1,9,17], 8208003360), ([1,10,10], 3287337600), ([1,10,11], 5911061120), ([1,10,12], 7349472480), ([1,10,13], 5975361440), ([1,10,14], 8125047480), ([1,10,15], 7310555360), ([1,10,16], 7652744800), ([1,10,17], 8198641920), ([1,11,11], 3794524160), ([1,11,12], 7850429440), ([1,11,13], 6205292800), ([1,11,14], 8413864120), ([1,11,15], 7605570560), ([1,11,16], 7277580800), ([1,11,17], 8654338560), ([1,12,12], 5546741760), ([1,12,13], 8918250880), ([1,12,14], 12516486840), ([1,12,15], 11769116800), ([1,12,16], 7645850240), ([1,12,17], 8873682720), ([1,13,13], 3470027456), ([1,13,14], 9201418000), ([1,13,15], 10093237280), ([1,13,16], 7347075680), ([1,13,17], 7882412160), ([1,14,14], 6708730320), ([1,14,15], 10927396240), ([1,14,16], 8160306320), ([1,14,17], 8967654960), ([1,15,15], 3992019360), ([1,15,16], 5176124800), ([1,15,17], 5897774400), ([1,16,16], 769123040), ([1,16,17], 1724694720), ([1,17,17], 333335520)]
theorem block005_data : block005 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5898088840 : Int) atom0335) (SparsePolynomial.scale (6018711240 : Int) atom0336)) (SparsePolynomial.merge (SparsePolynomial.scale (2000907360 : Int) atom0337) (SparsePolynomial.merge (SparsePolynomial.scale (3212404128 : Int) atom0338) (SparsePolynomial.scale (2905871040 : Int) atom0339)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2903290560 : Int) atom0340) (SparsePolynomial.scale (2951029440 : Int) atom0341)) (SparsePolynomial.merge (SparsePolynomial.scale (3174733760 : Int) atom0342) (SparsePolynomial.merge (SparsePolynomial.scale (5883494400 : Int) atom0343) (SparsePolynomial.scale (4456174040 : Int) atom0344))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6098833080 : Int) atom0345) (SparsePolynomial.scale (5959982600 : Int) atom0346)) (SparsePolynomial.merge (SparsePolynomial.scale (6391196200 : Int) atom0347) (SparsePolynomial.merge (SparsePolynomial.scale (6822409800 : Int) atom0348) (SparsePolynomial.scale (2336973120 : Int) atom0349)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3943380288 : Int) atom0350) (SparsePolynomial.scale (3334043520 : Int) atom0351)) (SparsePolynomial.merge (SparsePolynomial.scale (3358235520 : Int) atom0352) (SparsePolynomial.merge (SparsePolynomial.scale (3558392960 : Int) atom0353) (SparsePolynomial.scale (6159605760 : Int) atom0354)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4881594320 : Int) atom0355) (SparsePolynomial.scale (6576221880 : Int) atom0356)) (SparsePolynomial.merge (SparsePolynomial.scale (6516018800 : Int) atom0357) (SparsePolynomial.merge (SparsePolynomial.scale (7042158640 : Int) atom0358) (SparsePolynomial.scale (7568298480 : Int) atom0359)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2731883520 : Int) atom0360) (SparsePolynomial.scale (4672629120 : Int) atom0361)) (SparsePolynomial.merge (SparsePolynomial.scale (3937045632 : Int) atom0362) (SparsePolynomial.merge (SparsePolynomial.scale (4045591040 : Int) atom0363) (SparsePolynomial.scale (6538183680 : Int) atom0364))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5324168960 : Int) atom0365) (SparsePolynomial.scale (7156077240 : Int) atom0366)) (SparsePolynomial.merge (SparsePolynomial.scale (6966759680 : Int) atom0367) (SparsePolynomial.merge (SparsePolynomial.scale (7463345920 : Int) atom0368) (SparsePolynomial.scale (8011165440 : Int) atom0369)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3038632320 : Int) atom0370) (SparsePolynomial.scale (5210772480 : Int) atom0371)) (SparsePolynomial.merge (SparsePolynomial.scale (4660776320 : Int) atom0372) (SparsePolynomial.merge (SparsePolynomial.scale (6904803360 : Int) atom0373) (SparsePolynomial.scale (5640737120 : Int) atom0374))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7615402680 : Int) atom0375) (SparsePolynomial.scale (7207039520 : Int) atom0376)) (SparsePolynomial.merge (SparsePolynomial.scale (7686420640 : Int) atom0377) (SparsePolynomial.merge (SparsePolynomial.scale (8208003360 : Int) atom0378) (SparsePolynomial.scale (3287337600 : Int) atom0379)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5911061120 : Int) atom0380) (SparsePolynomial.scale (7349472480 : Int) atom0381)) (SparsePolynomial.merge (SparsePolynomial.scale (5975361440 : Int) atom0382) (SparsePolynomial.merge (SparsePolynomial.scale (8125047480 : Int) atom0383) (SparsePolynomial.scale (7310555360 : Int) atom0384))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7652744800 : Int) atom0385) (SparsePolynomial.scale (8198641920 : Int) atom0386)) (SparsePolynomial.merge (SparsePolynomial.scale (3794524160 : Int) atom0387) (SparsePolynomial.merge (SparsePolynomial.scale (7850429440 : Int) atom0388) (SparsePolynomial.scale (6205292800 : Int) atom0389)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8413864120 : Int) atom0390) (SparsePolynomial.scale (7605570560 : Int) atom0391)) (SparsePolynomial.merge (SparsePolynomial.scale (7277580800 : Int) atom0392) (SparsePolynomial.merge (SparsePolynomial.scale (8654338560 : Int) atom0393) (SparsePolynomial.scale (5546741760 : Int) atom0394)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8918250880 : Int) atom0395) (SparsePolynomial.scale (12516486840 : Int) atom0396)) (SparsePolynomial.merge (SparsePolynomial.scale (11769116800 : Int) atom0397) (SparsePolynomial.merge (SparsePolynomial.scale (7645850240 : Int) atom0398) (SparsePolynomial.scale (8873682720 : Int) atom0399)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3470027456 : Int) atom0400) (SparsePolynomial.scale (9201418000 : Int) atom0401)) (SparsePolynomial.merge (SparsePolynomial.scale (10093237280 : Int) atom0402) (SparsePolynomial.merge (SparsePolynomial.scale (7347075680 : Int) atom0403) (SparsePolynomial.scale (7882412160 : Int) atom0404))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6708730320 : Int) atom0405) (SparsePolynomial.scale (10927396240 : Int) atom0406)) (SparsePolynomial.merge (SparsePolynomial.scale (8160306320 : Int) atom0407) (SparsePolynomial.merge (SparsePolynomial.scale (8967654960 : Int) atom0408) (SparsePolynomial.scale (3992019360 : Int) atom0409)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5176124800 : Int) atom0410) (SparsePolynomial.scale (5897774400 : Int) atom0411)) (SparsePolynomial.merge (SparsePolynomial.scale (769123040 : Int) atom0412) (SparsePolynomial.merge (SparsePolynomial.scale (1724694720 : Int) atom0413) (SparsePolynomial.scale (333335520 : Int) atom0414)))))))) := by decide +kernel
theorem block005_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block005 := by
  rw [block005_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0335_nonneg g hg hA hB) (atom0336_nonneg g hg hA hB)) (add_nonneg (atom0337_nonneg g hg hA hB) (add_nonneg (atom0338_nonneg g hg hA hB) (atom0339_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0340_nonneg g hg hA hB) (atom0341_nonneg g hg hA hB)) (add_nonneg (atom0342_nonneg g hg hA hB) (add_nonneg (atom0343_nonneg g hg hA hB) (atom0344_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0345_nonneg g hg hA hB) (atom0346_nonneg g hg hA hB)) (add_nonneg (atom0347_nonneg g hg hA hB) (add_nonneg (atom0348_nonneg g hg hA hB) (atom0349_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0350_nonneg g hg hA hB) (atom0351_nonneg g hg hA hB)) (add_nonneg (atom0352_nonneg g hg hA hB) (add_nonneg (atom0353_nonneg g hg hA hB) (atom0354_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0355_nonneg g hg hA hB) (atom0356_nonneg g hg hA hB)) (add_nonneg (atom0357_nonneg g hg hA hB) (add_nonneg (atom0358_nonneg g hg hA hB) (atom0359_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0360_nonneg g hg hA hB) (atom0361_nonneg g hg hA hB)) (add_nonneg (atom0362_nonneg g hg hA hB) (add_nonneg (atom0363_nonneg g hg hA hB) (atom0364_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0365_nonneg g hg hA hB) (atom0366_nonneg g hg hA hB)) (add_nonneg (atom0367_nonneg g hg hA hB) (add_nonneg (atom0368_nonneg g hg hA hB) (atom0369_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0370_nonneg g hg hA hB) (atom0371_nonneg g hg hA hB)) (add_nonneg (atom0372_nonneg g hg hA hB) (add_nonneg (atom0373_nonneg g hg hA hB) (atom0374_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0375_nonneg g hg hA hB) (atom0376_nonneg g hg hA hB)) (add_nonneg (atom0377_nonneg g hg hA hB) (add_nonneg (atom0378_nonneg g hg hA hB) (atom0379_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0380_nonneg g hg hA hB) (atom0381_nonneg g hg hA hB)) (add_nonneg (atom0382_nonneg g hg hA hB) (add_nonneg (atom0383_nonneg g hg hA hB) (atom0384_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0385_nonneg g hg hA hB) (atom0386_nonneg g hg hA hB)) (add_nonneg (atom0387_nonneg g hg hA hB) (add_nonneg (atom0388_nonneg g hg hA hB) (atom0389_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0390_nonneg g hg hA hB) (atom0391_nonneg g hg hA hB)) (add_nonneg (atom0392_nonneg g hg hA hB) (add_nonneg (atom0393_nonneg g hg hA hB) (atom0394_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0395_nonneg g hg hA hB) (atom0396_nonneg g hg hA hB)) (add_nonneg (atom0397_nonneg g hg hA hB) (add_nonneg (atom0398_nonneg g hg hA hB) (atom0399_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0400_nonneg g hg hA hB) (atom0401_nonneg g hg hA hB)) (add_nonneg (atom0402_nonneg g hg hA hB) (add_nonneg (atom0403_nonneg g hg hA hB) (atom0404_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0405_nonneg g hg hA hB) (atom0406_nonneg g hg hA hB)) (add_nonneg (atom0407_nonneg g hg hA hB) (add_nonneg (atom0408_nonneg g hg hA hB) (atom0409_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0410_nonneg g hg hA hB) (atom0411_nonneg g hg hA hB)) (add_nonneg (atom0412_nonneg g hg hA hB) (add_nonneg (atom0413_nonneg g hg hA hB) (atom0414_nonneg g hg hA hB))))))))

end APPT.Finite18
