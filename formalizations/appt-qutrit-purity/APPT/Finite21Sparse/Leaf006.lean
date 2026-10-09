import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0336 : SparsePolynomial.Poly := [([0,13,16], 1)]
theorem eval_atom0336 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0336 = ((g 0) * (g 13) * (g 16)) := by
  norm_num [atom0336, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0336_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30929874548400 : Int) atom0336) := by
  rw [SparsePolynomial.eval_scale, eval_atom0336]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0337 : SparsePolynomial.Poly := [([0,13,17], 1)]
theorem eval_atom0337 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0337 = ((g 0) * (g 13) * (g 17)) := by
  norm_num [atom0337, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0337_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27676226793600 : Int) atom0337) := by
  rw [SparsePolynomial.eval_scale, eval_atom0337]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0338 : SparsePolynomial.Poly := [([0,13,18], 1)]
theorem eval_atom0338 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0338 = ((g 0) * (g 13) * (g 18)) := by
  norm_num [atom0338, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0338_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19355019465600 : Int) atom0338) := by
  rw [SparsePolynomial.eval_scale, eval_atom0338]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0339 : SparsePolynomial.Poly := [([0,13,19], 1)]
theorem eval_atom0339 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0339 = ((g 0) * (g 13) * (g 19)) := by
  norm_num [atom0339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0339_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14192212251600 : Int) atom0339) := by
  rw [SparsePolynomial.eval_scale, eval_atom0339]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0340 : SparsePolynomial.Poly := [([0,13,20], 1)]
theorem eval_atom0340 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0340 = ((g 0) * (g 13) * (g 20)) := by
  norm_num [atom0340, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0340_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10448028259200 : Int) atom0340) := by
  rw [SparsePolynomial.eval_scale, eval_atom0340]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0341 : SparsePolynomial.Poly := [([0,14,14], 1)]
theorem eval_atom0341 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0341 = ((g 0) * (g 14) * (g 14)) := by
  norm_num [atom0341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0341_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22957537881600 : Int) atom0341) := by
  rw [SparsePolynomial.eval_scale, eval_atom0341]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0342 : SparsePolynomial.Poly := [([0,14,15], 1)]
theorem eval_atom0342 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0342 = ((g 0) * (g 14) * (g 15)) := by
  norm_num [atom0342, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0342_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40599005328000 : Int) atom0342) := by
  rw [SparsePolynomial.eval_scale, eval_atom0342]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0343 : SparsePolynomial.Poly := [([0,14,16], 1)]
theorem eval_atom0343 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0343 = ((g 0) * (g 14) * (g 16)) := by
  norm_num [atom0343, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0343_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32015781705600 : Int) atom0343) := by
  rw [SparsePolynomial.eval_scale, eval_atom0343]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0344 : SparsePolynomial.Poly := [([0,14,17], 1)]
theorem eval_atom0344 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0344 = ((g 0) * (g 14) * (g 17)) := by
  norm_num [atom0344, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0344_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29965795171200 : Int) atom0344) := by
  rw [SparsePolynomial.eval_scale, eval_atom0344]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0345 : SparsePolynomial.Poly := [([0,14,18], 1)]
theorem eval_atom0345 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0345 = ((g 0) * (g 14) * (g 18)) := by
  norm_num [atom0345, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0345_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21942260726400 : Int) atom0345) := by
  rw [SparsePolynomial.eval_scale, eval_atom0345]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0346 : SparsePolynomial.Poly := [([0,14,19], 1)]
theorem eval_atom0346 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0346 = ((g 0) * (g 14) * (g 19)) := by
  norm_num [atom0346, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0346_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14664738614400 : Int) atom0346) := by
  rw [SparsePolynomial.eval_scale, eval_atom0346]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0347 : SparsePolynomial.Poly := [([0,14,20], 1)]
theorem eval_atom0347 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0347 = ((g 0) * (g 14) * (g 20)) := by
  norm_num [atom0347, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0347_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12517241385600 : Int) atom0347) := by
  rw [SparsePolynomial.eval_scale, eval_atom0347]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0348 : SparsePolynomial.Poly := [([0,15,15], 1)]
theorem eval_atom0348 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0348 = ((g 0) * (g 15) * (g 15)) := by
  norm_num [atom0348, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0348_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23040654336000 : Int) atom0348) := by
  rw [SparsePolynomial.eval_scale, eval_atom0348]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0349 : SparsePolynomial.Poly := [([0,15,16], 1)]
theorem eval_atom0349 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0349 = ((g 0) * (g 15) * (g 16)) := by
  norm_num [atom0349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0349_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39225167654400 : Int) atom0349) := by
  rw [SparsePolynomial.eval_scale, eval_atom0349]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0350 : SparsePolynomial.Poly := [([0,15,17], 1)]
theorem eval_atom0350 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0350 = ((g 0) * (g 15) * (g 17)) := by
  norm_num [atom0350, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0350_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40376131084800 : Int) atom0350) := by
  rw [SparsePolynomial.eval_scale, eval_atom0350]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0351 : SparsePolynomial.Poly := [([0,15,18], 1)]
theorem eval_atom0351 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0351 = ((g 0) * (g 15) * (g 18)) := by
  norm_num [atom0351, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0351_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34037154547200 : Int) atom0351) := by
  rw [SparsePolynomial.eval_scale, eval_atom0351]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0352 : SparsePolynomial.Poly := [([0,15,19], 1)]
theorem eval_atom0352 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0352 = ((g 0) * (g 15) * (g 19)) := by
  norm_num [atom0352, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0352_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19513520611200 : Int) atom0352) := by
  rw [SparsePolynomial.eval_scale, eval_atom0352]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0353 : SparsePolynomial.Poly := [([0,15,20], 1)]
theorem eval_atom0353 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0353 = ((g 0) * (g 15) * (g 20)) := by
  norm_num [atom0353, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0353_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20827437120000 : Int) atom0353) := by
  rw [SparsePolynomial.eval_scale, eval_atom0353]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0354 : SparsePolynomial.Poly := [([0,16,16], 1)]
theorem eval_atom0354 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0354 = ((g 0) * (g 16) * (g 16)) := by
  norm_num [atom0354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0354_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16982044692480 : Int) atom0354) := by
  rw [SparsePolynomial.eval_scale, eval_atom0354]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0355 : SparsePolynomial.Poly := [([0,16,17], 1)]
theorem eval_atom0355 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0355 = ((g 0) * (g 16) * (g 17)) := by
  norm_num [atom0355, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0355_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33350960563200 : Int) atom0355) := by
  rw [SparsePolynomial.eval_scale, eval_atom0355]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0356 : SparsePolynomial.Poly := [([0,16,18], 1)]
theorem eval_atom0356 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0356 = ((g 0) * (g 16) * (g 18)) := by
  norm_num [atom0356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0356_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35187254323200 : Int) atom0356) := by
  rw [SparsePolynomial.eval_scale, eval_atom0356]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0357 : SparsePolynomial.Poly := [([0,16,19], 1)]
theorem eval_atom0357 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0357 = ((g 0) * (g 16) * (g 19)) := by
  norm_num [atom0357, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0357_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20310858691200 : Int) atom0357) := by
  rw [SparsePolynomial.eval_scale, eval_atom0357]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0358 : SparsePolynomial.Poly := [([0,16,20], 1)]
theorem eval_atom0358 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0358 = ((g 0) * (g 16) * (g 20)) := by
  norm_num [atom0358, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0358_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22313868595200 : Int) atom0358) := by
  rw [SparsePolynomial.eval_scale, eval_atom0358]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0359 : SparsePolynomial.Poly := [([0,17,17], 1)]
theorem eval_atom0359 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0359 = ((g 0) * (g 17) * (g 17)) := by
  norm_num [atom0359, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0359_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17166447244800 : Int) atom0359) := by
  rw [SparsePolynomial.eval_scale, eval_atom0359]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0360 : SparsePolynomial.Poly := [([0,17,18], 1)]
theorem eval_atom0360 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0360 = ((g 0) * (g 17) * (g 18)) := by
  norm_num [atom0360, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0360_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36337354099200 : Int) atom0360) := by
  rw [SparsePolynomial.eval_scale, eval_atom0360]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0361 : SparsePolynomial.Poly := [([0,17,19], 1)]
theorem eval_atom0361 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0361 = ((g 0) * (g 17) * (g 19)) := by
  norm_num [atom0361, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0361_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20587269225600 : Int) atom0361) := by
  rw [SparsePolynomial.eval_scale, eval_atom0361]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0362 : SparsePolynomial.Poly := [([0,17,20], 1)]
theorem eval_atom0362 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0362 = ((g 0) * (g 17) * (g 20)) := by
  norm_num [atom0362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0362_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20398324262400 : Int) atom0362) := by
  rw [SparsePolynomial.eval_scale, eval_atom0362]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0363 : SparsePolynomial.Poly := [([0,18,18], 1)]
theorem eval_atom0363 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0363 = ((g 0) * (g 18) * (g 18)) := by
  norm_num [atom0363, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0363_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18743726937600 : Int) atom0363) := by
  rw [SparsePolynomial.eval_scale, eval_atom0363]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0364 : SparsePolynomial.Poly := [([0,18,19], 1)]
theorem eval_atom0364 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0364 = ((g 0) * (g 18) * (g 19)) := by
  norm_num [atom0364, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0364_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21384607305600 : Int) atom0364) := by
  rw [SparsePolynomial.eval_scale, eval_atom0364]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0365 : SparsePolynomial.Poly := [([0,18,20], 1)]
theorem eval_atom0365 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0365 = ((g 0) * (g 18) * (g 20)) := by
  norm_num [atom0365, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0365_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21884755737600 : Int) atom0365) := by
  rw [SparsePolynomial.eval_scale, eval_atom0365]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0366 : SparsePolynomial.Poly := [([0,19,19], 1)]
theorem eval_atom0366 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0366 = ((g 0) * (g 19) * (g 19)) := by
  norm_num [atom0366, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0366_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1655080560000 : Int) atom0366) := by
  rw [SparsePolynomial.eval_scale, eval_atom0366]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 0) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0367 : SparsePolynomial.Poly := [([0,19,20], 1)]
theorem eval_atom0367 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0367 = ((g 0) * (g 19) * (g 20)) := by
  norm_num [atom0367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0367_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2509440393600 : Int) atom0367) := by
  rw [SparsePolynomial.eval_scale, eval_atom0367]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 0) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0368 : SparsePolynomial.Poly := [([1,1,2], 1)]
theorem eval_atom0368 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0368 = ((g 1) * (g 1) * (g 2)) := by
  norm_num [atom0368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0368_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4803357888000 : Int) atom0368) := by
  rw [SparsePolynomial.eval_scale, eval_atom0368]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0369 : SparsePolynomial.Poly := [([1,1,3], 1)]
theorem eval_atom0369 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0369 = ((g 1) * (g 1) * (g 3)) := by
  norm_num [atom0369, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0369_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4117163904000 : Int) atom0369) := by
  rw [SparsePolynomial.eval_scale, eval_atom0369]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0370 : SparsePolynomial.Poly := [([1,1,4], 1)]
theorem eval_atom0370 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0370 = ((g 1) * (g 1) * (g 4)) := by
  norm_num [atom0370, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0370_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3430969920000 : Int) atom0370) := by
  rw [SparsePolynomial.eval_scale, eval_atom0370]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0371 : SparsePolynomial.Poly := [([1,1,5], 1)]
theorem eval_atom0371 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0371 = ((g 1) * (g 1) * (g 5)) := by
  norm_num [atom0371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0371_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4236153898752 : Int) atom0371) := by
  rw [SparsePolynomial.eval_scale, eval_atom0371]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0372 : SparsePolynomial.Poly := [([1,1,6], 1)]
theorem eval_atom0372 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0372 = ((g 1) * (g 1) * (g 6)) := by
  norm_num [atom0372, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0372_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4003284902400 : Int) atom0372) := by
  rw [SparsePolynomial.eval_scale, eval_atom0372]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0373 : SparsePolynomial.Poly := [([1,1,7], 1)]
theorem eval_atom0373 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0373 = ((g 1) * (g 1) * (g 7)) := by
  norm_num [atom0373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0373_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4770887243904 : Int) atom0373) := by
  rw [SparsePolynomial.eval_scale, eval_atom0373]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0374 : SparsePolynomial.Poly := [([1,1,8], 1)]
theorem eval_atom0374 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0374 = ((g 1) * (g 1) * (g 8)) := by
  norm_num [atom0374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0374_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4586868518400 : Int) atom0374) := by
  rw [SparsePolynomial.eval_scale, eval_atom0374]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0375 : SparsePolynomial.Poly := [([1,1,9], 1)]
theorem eval_atom0375 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0375 = ((g 1) * (g 1) * (g 9)) := by
  norm_num [atom0375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0375_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4327854451200 : Int) atom0375) := by
  rw [SparsePolynomial.eval_scale, eval_atom0375]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0376 : SparsePolynomial.Poly := [([1,1,10], 1)]
theorem eval_atom0376 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0376 = ((g 1) * (g 1) * (g 10)) := by
  norm_num [atom0376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0376_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4068840384000 : Int) atom0376) := by
  rw [SparsePolynomial.eval_scale, eval_atom0376]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0377 : SparsePolynomial.Poly := [([1,1,11], 1)]
theorem eval_atom0377 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0377 = ((g 1) * (g 1) * (g 11)) := by
  norm_num [atom0377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0377_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3497902732800 : Int) atom0377) := by
  rw [SparsePolynomial.eval_scale, eval_atom0377]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0378 : SparsePolynomial.Poly := [([1,1,12], 1)]
theorem eval_atom0378 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0378 = ((g 1) * (g 1) * (g 12)) := by
  norm_num [atom0378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0378_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (877411942400 : Int) atom0378) := by
  rw [SparsePolynomial.eval_scale, eval_atom0378]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0379 : SparsePolynomial.Poly := [([1,1,15], 1)]
theorem eval_atom0379 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0379 = ((g 1) * (g 1) * (g 15)) := by
  norm_num [atom0379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0379_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4103633318400 : Int) atom0379) := by
  rw [SparsePolynomial.eval_scale, eval_atom0379]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0380 : SparsePolynomial.Poly := [([1,1,17], 1)]
theorem eval_atom0380 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0380 = ((g 1) * (g 1) * (g 17)) := by
  norm_num [atom0380, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0380_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (393250636800 : Int) atom0380) := by
  rw [SparsePolynomial.eval_scale, eval_atom0380]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 1) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0381 : SparsePolynomial.Poly := [([1,2,2], 1)]
theorem eval_atom0381 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0381 = ((g 1) * (g 2) * (g 2)) := by
  norm_num [atom0381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0381_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9359299353600 : Int) atom0381) := by
  rw [SparsePolynomial.eval_scale, eval_atom0381]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0382 : SparsePolynomial.Poly := [([1,2,3], 1)]
theorem eval_atom0382 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0382 = ((g 1) * (g 2) * (g 3)) := by
  norm_num [atom0382, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0382_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17682542438400 : Int) atom0382) := by
  rw [SparsePolynomial.eval_scale, eval_atom0382]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0383 : SparsePolynomial.Poly := [([1,2,4], 1)]
theorem eval_atom0383 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0383 = ((g 1) * (g 2) * (g 4)) := by
  norm_num [atom0383, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0383_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16646486169600 : Int) atom0383) := by
  rw [SparsePolynomial.eval_scale, eval_atom0383]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0384 : SparsePolynomial.Poly := [([1,2,5], 1)]
theorem eval_atom0384 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0384 = ((g 1) * (g 2) * (g 5)) := by
  norm_num [atom0384, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0384_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18593185826304 : Int) atom0384) := by
  rw [SparsePolynomial.eval_scale, eval_atom0384]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0385 : SparsePolynomial.Poly := [([1,2,6], 1)]
theorem eval_atom0385 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0385 = ((g 1) * (g 2) * (g 6)) := by
  norm_num [atom0385, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0385_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18463779532800 : Int) atom0385) := by
  rw [SparsePolynomial.eval_scale, eval_atom0385]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0386 : SparsePolynomial.Poly := [([1,2,7], 1)]
theorem eval_atom0386 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0386 = ((g 1) * (g 2) * (g 7)) := by
  norm_num [atom0386, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0386_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20335315915008 : Int) atom0386) := by
  rw [SparsePolynomial.eval_scale, eval_atom0386]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0387 : SparsePolynomial.Poly := [([1,2,8], 1)]
theorem eval_atom0387 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0387 = ((g 1) * (g 2) * (g 8)) := by
  norm_num [atom0387, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0387_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20303610163200 : Int) atom0387) := by
  rw [SparsePolynomial.eval_scale, eval_atom0387]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0388 : SparsePolynomial.Poly := [([1,2,9], 1)]
theorem eval_atom0388 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0388 = ((g 1) * (g 2) * (g 9)) := by
  norm_num [atom0388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0388_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20121913728000 : Int) atom0388) := by
  rw [SparsePolynomial.eval_scale, eval_atom0388]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0389 : SparsePolynomial.Poly := [([1,2,10], 1)]
theorem eval_atom0389 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0389 = ((g 1) * (g 2) * (g 10)) := by
  norm_num [atom0389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0389_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19940217292800 : Int) atom0389) := by
  rw [SparsePolynomial.eval_scale, eval_atom0389]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0390 : SparsePolynomial.Poly := [([1,2,11], 1)]
theorem eval_atom0390 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0390 = ((g 1) * (g 2) * (g 11)) := by
  norm_num [atom0390, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0390_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19134673689600 : Int) atom0390) := by
  rw [SparsePolynomial.eval_scale, eval_atom0390]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0391 : SparsePolynomial.Poly := [([1,2,12], 1)]
theorem eval_atom0391 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0391 = ((g 1) * (g 2) * (g 12)) := by
  norm_num [atom0391, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0391_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14230023808000 : Int) atom0391) := by
  rw [SparsePolynomial.eval_scale, eval_atom0391]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0392 : SparsePolynomial.Poly := [([1,2,13], 1)]
theorem eval_atom0392 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0392 = ((g 1) * (g 2) * (g 13)) := by
  norm_num [atom0392, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0392_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12811531622400 : Int) atom0392) := by
  rw [SparsePolynomial.eval_scale, eval_atom0392]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0393 : SparsePolynomial.Poly := [([1,2,14], 1)]
theorem eval_atom0393 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0393 = ((g 1) * (g 2) * (g 14)) := by
  norm_num [atom0393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0393_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13147863321600 : Int) atom0393) := by
  rw [SparsePolynomial.eval_scale, eval_atom0393]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0394 : SparsePolynomial.Poly := [([1,2,15], 1)]
theorem eval_atom0394 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0394 = ((g 1) * (g 2) * (g 15)) := by
  norm_num [atom0394, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0394_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22298405068800 : Int) atom0394) := by
  rw [SparsePolynomial.eval_scale, eval_atom0394]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0395 : SparsePolynomial.Poly := [([1,2,16], 1)]
theorem eval_atom0395 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0395 = ((g 1) * (g 2) * (g 16)) := by
  norm_num [atom0395, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0395_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11832174950400 : Int) atom0395) := by
  rw [SparsePolynomial.eval_scale, eval_atom0395]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0396 : SparsePolynomial.Poly := [([1,2,17], 1)]
theorem eval_atom0396 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0396 = ((g 1) * (g 2) * (g 17)) := by
  norm_num [atom0396, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0396_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18674799091200 : Int) atom0396) := by
  rw [SparsePolynomial.eval_scale, eval_atom0396]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 2) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0397 : SparsePolynomial.Poly := [([1,2,18], 1)]
theorem eval_atom0397 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0397 = ((g 1) * (g 2) * (g 18)) := by
  norm_num [atom0397, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0397_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11176263705600 : Int) atom0397) := by
  rw [SparsePolynomial.eval_scale, eval_atom0397]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 2) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0398 : SparsePolynomial.Poly := [([1,2,19], 1)]
theorem eval_atom0398 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0398 = ((g 1) * (g 2) * (g 19)) := by
  norm_num [atom0398, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0398_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7996898246400 : Int) atom0398) := by
  rw [SparsePolynomial.eval_scale, eval_atom0398]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 2) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0399 : SparsePolynomial.Poly := [([1,2,20], 1)]
theorem eval_atom0399 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0399 = ((g 1) * (g 2) * (g 20)) := by
  norm_num [atom0399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0399_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7905405715200 : Int) atom0399) := by
  rw [SparsePolynomial.eval_scale, eval_atom0399]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 2) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0400 : SparsePolynomial.Poly := [([1,3,3], 1)]
theorem eval_atom0400 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0400 = ((g 1) * (g 3) * (g 3)) := by
  norm_num [atom0400, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0400_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7468883251200 : Int) atom0400) := by
  rw [SparsePolynomial.eval_scale, eval_atom0400]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0401 : SparsePolynomial.Poly := [([1,3,4], 1)]
theorem eval_atom0401 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0401 = ((g 1) * (g 3) * (g 4)) := by
  norm_num [atom0401, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0401_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14238041932800 : Int) atom0401) := by
  rw [SparsePolynomial.eval_scale, eval_atom0401]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0402 : SparsePolynomial.Poly := [([1,3,5], 1)]
theorem eval_atom0402 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0402 = ((g 1) * (g 3) * (g 5)) := by
  norm_num [atom0402, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0402_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16521073288704 : Int) atom0402) := by
  rw [SparsePolynomial.eval_scale, eval_atom0402]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0403 : SparsePolynomial.Poly := [([1,3,6], 1)]
theorem eval_atom0403 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0403 = ((g 1) * (g 3) * (g 6)) := by
  norm_num [atom0403, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0403_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16727998694400 : Int) atom0403) := by
  rw [SparsePolynomial.eval_scale, eval_atom0403]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0404 : SparsePolynomial.Poly := [([1,3,7], 1)]
theorem eval_atom0404 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0404 = ((g 1) * (g 3) * (g 7)) := by
  norm_num [atom0404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0404_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18935866775808 : Int) atom0404) := by
  rw [SparsePolynomial.eval_scale, eval_atom0404]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0405 : SparsePolynomial.Poly := [([1,3,8], 1)]
theorem eval_atom0405 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0405 = ((g 1) * (g 3) * (g 8)) := by
  norm_num [atom0405, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0405_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19240492723200 : Int) atom0405) := by
  rw [SparsePolynomial.eval_scale, eval_atom0405]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0406 : SparsePolynomial.Poly := [([1,3,9], 1)]
theorem eval_atom0406 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0406 = ((g 1) * (g 3) * (g 9)) := by
  norm_num [atom0406, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0406_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19395127987200 : Int) atom0406) := by
  rw [SparsePolynomial.eval_scale, eval_atom0406]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0407 : SparsePolynomial.Poly := [([1,3,10], 1)]
theorem eval_atom0407 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0407 = ((g 1) * (g 3) * (g 10)) := by
  norm_num [atom0407, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0407_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19549763251200 : Int) atom0407) := by
  rw [SparsePolynomial.eval_scale, eval_atom0407]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0408 : SparsePolynomial.Poly := [([1,3,11], 1)]
theorem eval_atom0408 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0408 = ((g 1) * (g 3) * (g 11)) := by
  norm_num [atom0408, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0408_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19080551347200 : Int) atom0408) := by
  rw [SparsePolynomial.eval_scale, eval_atom0408]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0409 : SparsePolynomial.Poly := [([1,3,12], 1)]
theorem eval_atom0409 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0409 = ((g 1) * (g 3) * (g 12)) := by
  norm_num [atom0409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0409_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14512233164800 : Int) atom0409) := by
  rw [SparsePolynomial.eval_scale, eval_atom0409]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0410 : SparsePolynomial.Poly := [([1,3,13], 1)]
theorem eval_atom0410 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0410 = ((g 1) * (g 3) * (g 13)) := by
  norm_num [atom0410, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0410_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13430072678400 : Int) atom0410) := by
  rw [SparsePolynomial.eval_scale, eval_atom0410]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0411 : SparsePolynomial.Poly := [([1,3,14], 1)]
theorem eval_atom0411 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0411 = ((g 1) * (g 3) * (g 14)) := by
  norm_num [atom0411, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0411_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14102736076800 : Int) atom0411) := by
  rw [SparsePolynomial.eval_scale, eval_atom0411]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0412 : SparsePolynomial.Poly := [([1,3,15], 1)]
theorem eval_atom0412 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0412 = ((g 1) * (g 3) * (g 15)) := by
  norm_num [atom0412, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0412_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23589609523200 : Int) atom0412) := by
  rw [SparsePolynomial.eval_scale, eval_atom0412]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0413 : SparsePolynomial.Poly := [([1,3,16], 1)]
theorem eval_atom0413 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0413 = ((g 1) * (g 3) * (g 16)) := by
  norm_num [atom0413, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0413_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14801172019200 : Int) atom0413) := by
  rw [SparsePolynomial.eval_scale, eval_atom0413]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0414 : SparsePolynomial.Poly := [([1,3,17], 1)]
theorem eval_atom0414 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0414 = ((g 1) * (g 3) * (g 17)) := by
  norm_num [atom0414, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0414_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20638666944000 : Int) atom0414) := by
  rw [SparsePolynomial.eval_scale, eval_atom0414]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0415 : SparsePolynomial.Poly := [([1,3,18], 1)]
theorem eval_atom0415 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0415 = ((g 1) * (g 3) * (g 18)) := by
  norm_num [atom0415, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0415_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15517648742400 : Int) atom0415) := by
  rw [SparsePolynomial.eval_scale, eval_atom0415]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 3) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block006 : SparsePolynomial.Poly := [([0,13,16], 30929874548400), ([0,13,17], 27676226793600), ([0,13,18], 19355019465600), ([0,13,19], 14192212251600), ([0,13,20], 10448028259200), ([0,14,14], 22957537881600), ([0,14,15], 40599005328000), ([0,14,16], 32015781705600), ([0,14,17], 29965795171200), ([0,14,18], 21942260726400), ([0,14,19], 14664738614400), ([0,14,20], 12517241385600), ([0,15,15], 23040654336000), ([0,15,16], 39225167654400), ([0,15,17], 40376131084800), ([0,15,18], 34037154547200), ([0,15,19], 19513520611200), ([0,15,20], 20827437120000), ([0,16,16], 16982044692480), ([0,16,17], 33350960563200), ([0,16,18], 35187254323200), ([0,16,19], 20310858691200), ([0,16,20], 22313868595200), ([0,17,17], 17166447244800), ([0,17,18], 36337354099200), ([0,17,19], 20587269225600), ([0,17,20], 20398324262400), ([0,18,18], 18743726937600), ([0,18,19], 21384607305600), ([0,18,20], 21884755737600), ([0,19,19], 1655080560000), ([0,19,20], 2509440393600), ([1,1,2], 4803357888000), ([1,1,3], 4117163904000), ([1,1,4], 3430969920000), ([1,1,5], 4236153898752), ([1,1,6], 4003284902400), ([1,1,7], 4770887243904), ([1,1,8], 4586868518400), ([1,1,9], 4327854451200), ([1,1,10], 4068840384000), ([1,1,11], 3497902732800), ([1,1,12], 877411942400), ([1,1,15], 4103633318400), ([1,1,17], 393250636800), ([1,2,2], 9359299353600), ([1,2,3], 17682542438400), ([1,2,4], 16646486169600), ([1,2,5], 18593185826304), ([1,2,6], 18463779532800), ([1,2,7], 20335315915008), ([1,2,8], 20303610163200), ([1,2,9], 20121913728000), ([1,2,10], 19940217292800), ([1,2,11], 19134673689600), ([1,2,12], 14230023808000), ([1,2,13], 12811531622400), ([1,2,14], 13147863321600), ([1,2,15], 22298405068800), ([1,2,16], 11832174950400), ([1,2,17], 18674799091200), ([1,2,18], 11176263705600), ([1,2,19], 7996898246400), ([1,2,20], 7905405715200), ([1,3,3], 7468883251200), ([1,3,4], 14238041932800), ([1,3,5], 16521073288704), ([1,3,6], 16727998694400), ([1,3,7], 18935866775808), ([1,3,8], 19240492723200), ([1,3,9], 19395127987200), ([1,3,10], 19549763251200), ([1,3,11], 19080551347200), ([1,3,12], 14512233164800), ([1,3,13], 13430072678400), ([1,3,14], 14102736076800), ([1,3,15], 23589609523200), ([1,3,16], 14801172019200), ([1,3,17], 20638666944000), ([1,3,18], 15517648742400)]
theorem block006_data : block006 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30929874548400 : Int) atom0336) (SparsePolynomial.scale (27676226793600 : Int) atom0337)) (SparsePolynomial.merge (SparsePolynomial.scale (19355019465600 : Int) atom0338) (SparsePolynomial.merge (SparsePolynomial.scale (14192212251600 : Int) atom0339) (SparsePolynomial.scale (10448028259200 : Int) atom0340)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22957537881600 : Int) atom0341) (SparsePolynomial.scale (40599005328000 : Int) atom0342)) (SparsePolynomial.merge (SparsePolynomial.scale (32015781705600 : Int) atom0343) (SparsePolynomial.merge (SparsePolynomial.scale (29965795171200 : Int) atom0344) (SparsePolynomial.scale (21942260726400 : Int) atom0345))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14664738614400 : Int) atom0346) (SparsePolynomial.scale (12517241385600 : Int) atom0347)) (SparsePolynomial.merge (SparsePolynomial.scale (23040654336000 : Int) atom0348) (SparsePolynomial.merge (SparsePolynomial.scale (39225167654400 : Int) atom0349) (SparsePolynomial.scale (40376131084800 : Int) atom0350)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (34037154547200 : Int) atom0351) (SparsePolynomial.scale (19513520611200 : Int) atom0352)) (SparsePolynomial.merge (SparsePolynomial.scale (20827437120000 : Int) atom0353) (SparsePolynomial.merge (SparsePolynomial.scale (16982044692480 : Int) atom0354) (SparsePolynomial.scale (33350960563200 : Int) atom0355)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (35187254323200 : Int) atom0356) (SparsePolynomial.scale (20310858691200 : Int) atom0357)) (SparsePolynomial.merge (SparsePolynomial.scale (22313868595200 : Int) atom0358) (SparsePolynomial.merge (SparsePolynomial.scale (17166447244800 : Int) atom0359) (SparsePolynomial.scale (36337354099200 : Int) atom0360)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20587269225600 : Int) atom0361) (SparsePolynomial.scale (20398324262400 : Int) atom0362)) (SparsePolynomial.merge (SparsePolynomial.scale (18743726937600 : Int) atom0363) (SparsePolynomial.merge (SparsePolynomial.scale (21384607305600 : Int) atom0364) (SparsePolynomial.scale (21884755737600 : Int) atom0365))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1655080560000 : Int) atom0366) (SparsePolynomial.scale (2509440393600 : Int) atom0367)) (SparsePolynomial.merge (SparsePolynomial.scale (4803357888000 : Int) atom0368) (SparsePolynomial.merge (SparsePolynomial.scale (4117163904000 : Int) atom0369) (SparsePolynomial.scale (3430969920000 : Int) atom0370)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4236153898752 : Int) atom0371) (SparsePolynomial.scale (4003284902400 : Int) atom0372)) (SparsePolynomial.merge (SparsePolynomial.scale (4770887243904 : Int) atom0373) (SparsePolynomial.merge (SparsePolynomial.scale (4586868518400 : Int) atom0374) (SparsePolynomial.scale (4327854451200 : Int) atom0375))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (4068840384000 : Int) atom0376) (SparsePolynomial.scale (3497902732800 : Int) atom0377)) (SparsePolynomial.merge (SparsePolynomial.scale (877411942400 : Int) atom0378) (SparsePolynomial.merge (SparsePolynomial.scale (4103633318400 : Int) atom0379) (SparsePolynomial.scale (393250636800 : Int) atom0380)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9359299353600 : Int) atom0381) (SparsePolynomial.scale (17682542438400 : Int) atom0382)) (SparsePolynomial.merge (SparsePolynomial.scale (16646486169600 : Int) atom0383) (SparsePolynomial.merge (SparsePolynomial.scale (18593185826304 : Int) atom0384) (SparsePolynomial.scale (18463779532800 : Int) atom0385))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20335315915008 : Int) atom0386) (SparsePolynomial.scale (20303610163200 : Int) atom0387)) (SparsePolynomial.merge (SparsePolynomial.scale (20121913728000 : Int) atom0388) (SparsePolynomial.merge (SparsePolynomial.scale (19940217292800 : Int) atom0389) (SparsePolynomial.scale (19134673689600 : Int) atom0390)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14230023808000 : Int) atom0391) (SparsePolynomial.scale (12811531622400 : Int) atom0392)) (SparsePolynomial.merge (SparsePolynomial.scale (13147863321600 : Int) atom0393) (SparsePolynomial.merge (SparsePolynomial.scale (22298405068800 : Int) atom0394) (SparsePolynomial.scale (11832174950400 : Int) atom0395)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (18674799091200 : Int) atom0396) (SparsePolynomial.scale (11176263705600 : Int) atom0397)) (SparsePolynomial.merge (SparsePolynomial.scale (7996898246400 : Int) atom0398) (SparsePolynomial.merge (SparsePolynomial.scale (7905405715200 : Int) atom0399) (SparsePolynomial.scale (7468883251200 : Int) atom0400)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14238041932800 : Int) atom0401) (SparsePolynomial.scale (16521073288704 : Int) atom0402)) (SparsePolynomial.merge (SparsePolynomial.scale (16727998694400 : Int) atom0403) (SparsePolynomial.merge (SparsePolynomial.scale (18935866775808 : Int) atom0404) (SparsePolynomial.scale (19240492723200 : Int) atom0405))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19395127987200 : Int) atom0406) (SparsePolynomial.scale (19549763251200 : Int) atom0407)) (SparsePolynomial.merge (SparsePolynomial.scale (19080551347200 : Int) atom0408) (SparsePolynomial.merge (SparsePolynomial.scale (14512233164800 : Int) atom0409) (SparsePolynomial.scale (13430072678400 : Int) atom0410)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (14102736076800 : Int) atom0411) (SparsePolynomial.scale (23589609523200 : Int) atom0412)) (SparsePolynomial.merge (SparsePolynomial.scale (14801172019200 : Int) atom0413) (SparsePolynomial.merge (SparsePolynomial.scale (20638666944000 : Int) atom0414) (SparsePolynomial.scale (15517648742400 : Int) atom0415)))))))) := by decide +kernel
theorem block006_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block006 := by
  rw [block006_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0336_nonneg g hg hA hB) (atom0337_nonneg g hg hA hB)) (add_nonneg (atom0338_nonneg g hg hA hB) (add_nonneg (atom0339_nonneg g hg hA hB) (atom0340_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0341_nonneg g hg hA hB) (atom0342_nonneg g hg hA hB)) (add_nonneg (atom0343_nonneg g hg hA hB) (add_nonneg (atom0344_nonneg g hg hA hB) (atom0345_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0346_nonneg g hg hA hB) (atom0347_nonneg g hg hA hB)) (add_nonneg (atom0348_nonneg g hg hA hB) (add_nonneg (atom0349_nonneg g hg hA hB) (atom0350_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0351_nonneg g hg hA hB) (atom0352_nonneg g hg hA hB)) (add_nonneg (atom0353_nonneg g hg hA hB) (add_nonneg (atom0354_nonneg g hg hA hB) (atom0355_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0356_nonneg g hg hA hB) (atom0357_nonneg g hg hA hB)) (add_nonneg (atom0358_nonneg g hg hA hB) (add_nonneg (atom0359_nonneg g hg hA hB) (atom0360_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0361_nonneg g hg hA hB) (atom0362_nonneg g hg hA hB)) (add_nonneg (atom0363_nonneg g hg hA hB) (add_nonneg (atom0364_nonneg g hg hA hB) (atom0365_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0366_nonneg g hg hA hB) (atom0367_nonneg g hg hA hB)) (add_nonneg (atom0368_nonneg g hg hA hB) (add_nonneg (atom0369_nonneg g hg hA hB) (atom0370_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0371_nonneg g hg hA hB) (atom0372_nonneg g hg hA hB)) (add_nonneg (atom0373_nonneg g hg hA hB) (add_nonneg (atom0374_nonneg g hg hA hB) (atom0375_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0376_nonneg g hg hA hB) (atom0377_nonneg g hg hA hB)) (add_nonneg (atom0378_nonneg g hg hA hB) (add_nonneg (atom0379_nonneg g hg hA hB) (atom0380_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0381_nonneg g hg hA hB) (atom0382_nonneg g hg hA hB)) (add_nonneg (atom0383_nonneg g hg hA hB) (add_nonneg (atom0384_nonneg g hg hA hB) (atom0385_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0386_nonneg g hg hA hB) (atom0387_nonneg g hg hA hB)) (add_nonneg (atom0388_nonneg g hg hA hB) (add_nonneg (atom0389_nonneg g hg hA hB) (atom0390_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0391_nonneg g hg hA hB) (atom0392_nonneg g hg hA hB)) (add_nonneg (atom0393_nonneg g hg hA hB) (add_nonneg (atom0394_nonneg g hg hA hB) (atom0395_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0396_nonneg g hg hA hB) (atom0397_nonneg g hg hA hB)) (add_nonneg (atom0398_nonneg g hg hA hB) (add_nonneg (atom0399_nonneg g hg hA hB) (atom0400_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0401_nonneg g hg hA hB) (atom0402_nonneg g hg hA hB)) (add_nonneg (atom0403_nonneg g hg hA hB) (add_nonneg (atom0404_nonneg g hg hA hB) (atom0405_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0406_nonneg g hg hA hB) (atom0407_nonneg g hg hA hB)) (add_nonneg (atom0408_nonneg g hg hA hB) (add_nonneg (atom0409_nonneg g hg hA hB) (atom0410_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0411_nonneg g hg hA hB) (atom0412_nonneg g hg hA hB)) (add_nonneg (atom0413_nonneg g hg hA hB) (add_nonneg (atom0414_nonneg g hg hA hB) (atom0415_nonneg g hg hA hB))))))))

end APPT.Finite21
